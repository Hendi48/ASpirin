unit ASProtect;

interface

uses Windows, Classes, DebuggerCore, SysUtils, Generics.Collections, Utils, RolyPoly;

type
  TASDebugger = class(TDebuggerCore)
  private
    FBaseOfData: NativeUInt;
    FPESections: array of TImageSectionHeader;

    FCounter: Integer;

    FGuardStart, FGuardEnd: NativeUInt;
    FGuardStepping: Boolean;
    FGuardAddrs: TList<NativeUInt>;

    FASRegion: TMemoryRegion; // Region to scan for proc reveal point
    FGetProcResultAddr, FProcTypeAddr: NativeUInt; // API in eax
    FProcRevealEvent: THandle;
    FProcAddr: Pointer;
    FProcIsJmp: Boolean;

    FRolyPoly: TRolyPoly;
    FPolyCode: TList<TFixedPolyCode>;

    FOEP: NativeUInt;

    function IsGuardedAddress(Address: NativeUInt): Boolean;
    function ProcessGuardedAccess(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal;

    procedure RestoreStolenOEPForMSVC6(hThread: THandle; var OEP: NativeUInt; IAT: NativeUInt);
    procedure FixupAPICallSites(hThread: THandle);
    procedure FinishUnpacking;

    procedure InitTracing;
  protected
    procedure OnDebugStart(var hPE: THandle); override;
    procedure OnHardwareBreakpoint(hThread: THandle; BPA: NativeUInt; var C: TContext); override;
    function OnAccessViolation(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal; override;
    function OnSinglestep(BPA: NativeUInt): Cardinal; override;
  public
    destructor Destroy; override;
  end;

  TASTracer = class(TThread)
  private
    FDebugger: TASDebugger;
    FGuardAddrs: TList<NativeUInt>;
    FTraceThread: THandle;

    procedure Log(MsgType: TLogMsgType; const Msg: string);

    function DoTrace(Address: NativeUInt): NativeUInt;
  protected
    procedure Execute; override;
  public
    constructor Create(ADebugger: TASDebugger; ATraceThread: THandle);
  end;

implementation

uses Dumper, Patcher, RestoreLibCode;

{$POINTERMATH ON}

{ TASDebugger }

destructor TASDebugger.Destroy;
begin
  FGuardAddrs.Free;
  FPolyCode.Free;

  inherited;
end;

procedure TASDebugger.OnDebugStart(var hPE: THandle);
var
  Buf, BufAlloc: PByte;
  Sect: PImageSectionHeader;
  i: Integer;
  NumRead: Cardinal;
begin
  FPolyCode := TObjectList<TFixedPolyCode>.Create;

  if (hPE = 0) or (hPE = INVALID_HANDLE_VALUE) then
  begin
    hPE := CreateFile(PChar(FExecutable), GENERIC_READ, FILE_SHARE_READ, nil, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, 0);
    if hPE = INVALID_HANDLE_VALUE then
      RaiseLastOSError;
  end;

  SetFilePointer(hPE, 0, nil, FILE_BEGIN);

  GetMem(BufAlloc, $1000);
  try
    if not ReadFile(hPE, BufAlloc^, $1000, NumRead, nil) then
      RaiseLastOSError;

    Buf := BufAlloc;
    Inc(Buf, PImageDosHeader(Buf)^._lfanew);
    Pointer(Sect) := Buf + SizeOf(TImageNTHeaders);

    SetLength(FPESections, PImageNTHeaders(Buf).FileHeader.NumberOfSections);
    for i := 0 to High(FPESections) do
      FPESections[i] := Sect[i];

    FBaseOfData := PImageNTHeaders(Buf).OptionalHeader.BaseOfData;
  finally
    FreeMem(BufAlloc);
  end;

  FGuardAddrs := TList<NativeUInt>.Create;

  SetBreakpoint(FImageBase + $1000, hwWrite);
end;

procedure TASDebugger.OnHardwareBreakpoint(hThread: THandle; BPA: NativeUInt; var C: TContext);
const
  CALL = 0;
  JMP = 1;
var
  OpTypes: array[0..1] of Byte;
begin
  if BPA = FImageBase + $1000 then
  begin
    Log(ltGood, 'HIT FROM ' + IntToHex(C.Eip, 8));
    Dec(FCounter);
  end
  else if BPA = FGetProcResultAddr then
  begin
    //Log(ltGood, Format('-> %X', [C.Eax]));
    FProcAddr := Pointer(C.Eax);
  end
  else if BPA = FProcTypeAddr then
  begin
    SuspendThread(hThread);

    // Many thanks to pstolarz for his extensive documentation
    // https://github.com/pstolarz/asprext/tree/master/analysis/1.6x/aip
    if not RPM(C.Eax + $4A, @OpTypes, 2) then
      raise Exception.Create('RPM for env failed');

    if (Byte(C.Edx) <> OpTypes[CALL]) and (Byte(C.Edx) <> OpTypes[JMP]) then
      raise Exception.Create('Op type fault');

    FProcIsJmp := Byte(C.Edx) = OpTypes[JMP];
    if FProcIsJmp then
      Log(ltGood, Format('-> %p, jmp', [FProcAddr]))
    else
      Log(ltGood, Format('-> %p, call', [FProcAddr]));

    SetEvent(FProcRevealEvent);
  end;
end;

function TASDebugger.OnSinglestep(BPA: NativeUInt): Cardinal;
var
  OldProt: Cardinal;
begin
  if FGuardStepping then
  begin
    VirtualProtectEx(FProcess.hProcess, Pointer(FGuardStart), FGuardEnd - FGuardStart, PAGE_NOACCESS, OldProt);
    FGuardStepping := False;
    Result := DBG_CONTINUE;
  end
  else
    Result := inherited;
end;

function TASDebugger.OnAccessViolation(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal;
var
  OldProt: Cardinal;
  i: Integer;
begin
  if FRolyPoly <> nil then
    Exit(FRolyPoly.OnAccessViolation(hThread, ExcRecord));

  if FGetProcResultAddr <> 0 then
  begin
    inherited;
    WaitForSingleObject(Handle, INFINITE);
  end;

  if not IsGuardedAddress(ExcRecord.ExceptionInformation[1]) then
  begin
    Inc(FCounter);
    if FCounter = 16 then  // FIXME this is quite the hack, some require 17
    begin
      FetchMemoryRegions;

      for i := 0 to High(FMemRegions) do
        if FMemRegions[i].Contains(NativeUInt(ExcRecord.ExceptionAddress)) then
        begin
          FASRegion := FMemRegions[i];
          Break;
        end;

      Log(ltGood, Format('AS region: %X~%X', [FASRegion.Address, FASRegion.Address + FASRegion.Size]));

      FGuardStart := FImageBase + FPESections[0].VirtualAddress;
      FGuardEnd := FImageBase + FBaseOfData;
      VirtualProtectEx(FProcess.hProcess, Pointer(FGuardStart), FGuardEnd - FGuardStart, PAGE_NOACCESS, OldProt);
    end;

    Exit(inherited);
  end;

  Result := ProcessGuardedAccess(hThread, ExcRecord);
end;

function TASDebugger.IsGuardedAddress(Address: NativeUInt): Boolean;
begin
  if FGuardStart = 0 then
    Exit(False);

  Result := (Address >= FGuardStart) and (Address < FGuardEnd);
end;

function TASDebugger.ProcessGuardedAccess(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal;
var
  OldProt: Cardinal;
  C: TContext;
  OEP: NativeUInt;
begin
  Log(ltInfo, Format('[Guard] %X', [ExcRecord.ExceptionInformation[1]]));

  VirtualProtectEx(FProcess.hProcess, Pointer(FGuardStart), FGuardEnd - FGuardStart, PAGE_EXECUTE_READWRITE, OldProt);

  if NativeUInt(ExcRecord.ExceptionAddress) > FGuardEnd then
  begin
    FGuardAddrs.Add(ExcRecord.ExceptionInformation[1]);

    if FGuardAddrs.Count > 1000 then
      raise Exception.Create('Fast-fail: Page guarding installed too early. Please try again.');

    // Single-step, then re-protect in OnHardwareBreakpoint
    FGuardStepping := True;
    C.ContextFlags := CONTEXT_CONTROL;
    if not GetThreadContext(hThread, C) then
      RaiseLastOSError;
    C.EFlags := C.EFlags or $100;
    if not SetThreadContext(hThread, C) then
      RaiseLastOSError;
  end
  else
  begin
    Log(ltGood, Format('OEP: 0x%p', [ExcRecord.ExceptionAddress]));

    OEP := NativeUInt(ExcRecord.ExceptionAddress);
    RestoreStolenOEPForMSVC6(hThread, OEP, FImageBase + FBaseOfData);

    VirtualProtectEx(FProcess.hProcess, Pointer(FGuardStart), FGuardEnd - FGuardStart, PAGE_EXECUTE_READ, OldProt);

    FOEP := OEP;

    if FGuardAddrs.Count > 0 then
      FixupAPICallSites(hThread)
    else
      FinishUnpacking;
  end;

  Result := DBG_CONTINUE;
end;

procedure TASDebugger.FixupAPICallSites(hThread: THandle);
begin
  InitTracing;

  SuspendThread(hThread);

  ResetBreakpoint(Pointer(FImageBase + $1000));
  SetBreakpoint(FGetProcResultAddr);
  SetBreakpoint(FProcTypeAddr);

  Log(ltInfo, 'Begin tracing...');

  FProcRevealEvent := CreateEvent(nil, False, False, nil);

  TASTracer.Create(Self, hThread);
end;

procedure TASDebugger.RestoreStolenOEPForMSVC6(hThread: THandle; var OEP: NativeUInt; IAT: NativeUInt);
const
  RESTORE_DATA: array[0..45] of Byte = (
    $55, $8B, $EC, $6A, $FF,
    $68, 0, 0, 0, 0, // stru
    $68, 0, 0, 0, 0, // except handler
    $64, $A1, $00, $00, $00, $00, $50, $64, $89, $25, $00, $00, $00, $00,
    $83, $EC, $58,
    $53, $56, $57,
    $89, $65, $E8,
    $FF, $15, 0, 0, 0, 0, // call ds:GetVersion
    $33, $D2
  );
var
  C: TContext;
  CheckBuf: array[0..2] of Byte;
  IATData: array[0..511] of NativeUInt;
  RestoreBuf: array[0..High(RESTORE_DATA)] of Byte;
  StackData: array[0..1] of NativeUInt;
  NumWritten: NativeUInt;
  i: Cardinal;
  GetVerAddr: NativeUInt;
begin
  RPM(OEP, @CheckBuf, 2);

  // mov dl, ah
  if (CheckBuf[0] <> $8A) or (CheckBuf[1] <> $D4) then
    Exit;

  Log(ltInfo, 'Stolen MSVC6 OEP detected.');

  RPM(OEP - Cardinal(Length(RESTORE_DATA)) - 3, @CheckBuf, 3);
  if (CheckBuf[0] <> $C2) and (CheckBuf[2] <> $C3) then
  begin
    Log(ltFatal, 'Stolen OEP gap mismatch.');
    Exit;
  end;

  Move(RESTORE_DATA, RestoreBuf, Length(RestoreBuf));
  Dec(OEP, Length(RestoreBuf));

  GetVerAddr := NativeUInt(GetProcAddress(GetModuleHandle(kernel32), 'GetVersion'));

  RPM(IAT, @IATData, SizeOf(IATData));
  for i := 0 to High(IATData) do
    if IATData[i] = GetVerAddr then
    begin
      PCardinal(@RestoreBuf[Length(RestoreBuf) - 6])^ := IAT + i * 4;
      Break;
    end;

  if PCardinal(@RestoreBuf[Length(RestoreBuf) - 6])^ = 0 then
  begin
    Log(ltFatal, 'Unable to find GetVersion in IAT.');
    Exit;
  end;

  C.ContextFlags := CONTEXT_INTEGER or CONTEXT_CONTROL;
  if not GetThreadContext(hThread, C) then
    RaiseLastOSError;

  if C.Esp <> C.Ebp - $74 then
  begin
    Log(ltFatal, Format('Stack frame mismatch: esp=%x, ebp=%x', [C.Esp, C.Ebp]));
    Exit;
  end;

  RPM(C.Ebp - 3 * SizeOf(NativeUInt), @StackData, SizeOf(StackData));

  PCardinal(@RestoreBuf[6])^ := StackData[1];
  PCardinal(@RestoreBuf[11])^ := StackData[0];

  WriteProcessMemory(FProcess.hProcess, Pointer(OEP), @RestoreBuf, Length(RestoreBuf), NumWritten);

  Log(ltGood, Format('Correct OEP: 0x%p', [Pointer(OEP)]));
end;

procedure TASDebugger.FinishUnpacking;
var
  FN: string;
begin
  FN := ExtractFilePath(FExecutable) + ChangeFileExt(ExtractFileName(FExecutable), 'U' + ExtractFileExt(FExecutable));
  with TDumper.Create(FProcess, FImageBase, FOEP, FImageBase + FBaseOfData) do
  begin
    PolyCode := FPolyCode;
    DumpToFile(FN, Process());
    Free;
  end;

  with TPatcher.Create(FN) do
  begin
    Process;
    Free;
  end;

  FHideThreadEnd := True;
  TerminateProcess(FProcess.hProcess, 0);
  Log(ltGood, 'Operation completed successfully.');
end;

procedure TASDebugger.InitTracing;
var
  ASData: PByte;
begin
  if FASRegion.Size = 0 then
    raise Exception.Create('ASRegion not set');

  GetMem(ASData, FASRegion.Size);
  try
    if not RPM(FASRegion.Address, ASData, FASRegion.Size) then
      raise Exception.Create('Unable to read ASRegion');

    FGetProcResultAddr := FindDynamic('668B4DEC668B55E88B45F4E8????????8945FC', ASData, FASRegion.Size);
    if FGetProcResultAddr = 0 then
      raise Exception.Create('Failed to find proc reveal point');

    FProcTypeAddr := FindDynamic('8BD00255??8B4DFC8B45F4', ASData + FGetProcResultAddr + 16, FASRegion.Size - FGetProcResultAddr - 16);
    if FProcTypeAddr = 0 then
      raise Exception.Create('Failed to find ref type');

    Inc(FProcTypeAddr, FASRegion.Address + FGetProcResultAddr + 16 + 11);
    Inc(FGetProcResultAddr, FASRegion.Address + 16);

    Log(ltGood, 'GetProcResultAddr: ' + IntToHex(FGetProcResultAddr, 8));
    Log(ltGood, 'ProcTypeAddr: ' + IntToHex(FProcTypeAddr, 8));
  finally
    FreeMem(ASData);
  end;
end;

{ TASTracer }

constructor TASTracer.Create(ADebugger: TASDebugger; ATraceThread: THandle);
begin
  FDebugger := ADebugger;
  FGuardAddrs := FDebugger.FGuardAddrs;
  FTraceThread := ATraceThread;

  FreeOnTerminate := True;

  inherited Create(False);
end;

procedure TASTracer.Execute;
var
  i: Integer;
  IAT, SiteAddr, Target, SiteTarget, NumWritten: NativeUInt;
  SiteSet: TList<NativeUInt>;
  Site: array[0..5] of Byte;
  IsJmp: Boolean;
  IATData: array[0..511] of NativeUInt;
  IATMap: TDictionary<NativeUInt, NativeUInt>;
  StolenData: TBytes;
  LastExtent: NativeUInt;
begin
  try
  SiteSet := TList<NativeUInt>.Create;
  IATMap := TDictionary<NativeUInt, NativeUInt>.Create;

  FGuardAddrs.Sort;
  SiteSet.Add(FGuardAddrs[0] - 1);
  for i := 1 to FGuardAddrs.Count - 1 do
    if (FGuardAddrs[i] - 1) >= SiteSet.Last + 6 then
      SiteSet.Add(FGuardAddrs[i] - 1);

  Log(ltInfo, Format('Deduced %d call sites from %d accesses', [SiteSet.Count, FGuardAddrs.Count]));

  IAT := FDebugger.FImageBase + FDebugger.FBaseOfData;
  FDebugger.RPM(IAT, @IATData, SizeOf(IATData));
  for i := 0 to High(IATData) do
    IATMap.AddOrSetValue(IATData[i], IAT + Cardinal(i) * 4);

  IsJmp := False;
  Target := 0;
  LastExtent := 0;

  for SiteAddr in SiteSet do
  begin
    if SiteAddr + 1 < LastExtent then
      Continue;

    if not FDebugger.RPM(SiteAddr, @Site, 6) then
      RaiseLastOSError;

    if Site[0] = $E8 then // TODO should check if PCardinal(@Site[1]) is mapped in case this is in fact the case below with an unfortunate byte in front
    begin
      //Target := PCardinal(@Site[1])^ + SiteAddr + 5;
      Target := DoTrace(SiteAddr);
      IsJmp := FDebugger.FProcIsJmp;
    end
    else if (Site[1] = $E9) or (Site[1] = $68) then
    begin
      if Site[1] = $E9 then
      begin
        SiteTarget := PCardinal(@Site[2])^ + SiteAddr + 6;
        Log(ltInfo, Format('Stolen: JMP at %X -> %X', [SiteAddr + 1, SiteTarget]));
      end
      else
      begin
        SiteTarget := PCardinal(@Site[2])^;
        Log(ltInfo, Format('Stolen: PUSH at %X -> %X', [SiteAddr + 1, SiteTarget]));
      end;

      if SiteTarget and $FFF <> 0 then
      begin
        Log(ltInfo, '(skipping)');
        Continue;
      end;

      StolenData := GetStolenCode(SiteAddr + 1, SiteTarget, FDebugger.RPM);
      if StolenData <> nil then
        WriteProcessMemory(FDebugger.FProcess.hProcess, Pointer(SiteAddr + 1), @StolenData[0], Length(StolenData), NumWritten)
      else
      begin
        FDebugger.FRolyPoly := TRolyPoly.Create(FDebugger.FProcess.hProcess, FTraceThread, SiteTarget, FDebugger.FASRegion, Log);
        FDebugger.FPolyCode.Add(FDebugger.FRolyPoly.Run);
        FDebugger.FPolyCode.Last.Origin := SiteAddr + 1;
        FreeAndNil(FDebugger.FRolyPoly);
      end;

      LastExtent := SiteAddr + 1 + Cardinal(Length(StolenData));
      Continue;
    end
    else
    begin
      Log(ltFatal, Format('Unknown call site at %X: %02X %02X %02X %02X %02X %02X', [SiteAddr, Site[0], Site[1], Site[2], Site[3], Site[4], Site[5]]));
      Continue;
    end;

    if not IATMap.ContainsKey(Target) then
    begin
      Log(ltFatal, Format('Not in IAT: %X (from %X)', [Target, SiteAddr]));
      Continue;
    end;

    // Turn the relative call/jmp into call/jmp dword ptr [iat]
    Site[0] := $FF;
    Site[1] := $15 + Ord(IsJmp) * $10;
    PCardinal(@Site[2])^ := IATMap[Target];
    WriteProcessMemory(FDebugger.FProcess.hProcess, Pointer(SiteAddr), @Site, 6, NumWritten)
  end;

  IATMap.Free;
  SiteSet.Free;

  FDebugger.FinishUnpacking;
  except
    Log(ltFatal, Exception(ExceptObject).Message);
  end;
end;

function TASTracer.DoTrace(Address: NativeUInt): NativeUInt;
const
  NullBytes: array[0..31] of Byte = (0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
var
  C: TContext;
  OldEsp: Cardinal;
  Written: NativeUInt;
begin
  Log(ltInfo, Format('Trace: %X', [Address]));

  C.ContextFlags := CONTEXT_CONTROL;
  if not GetThreadContext(FTraceThread, C) then
    RaiseLastOSError;

  C.Eip := Address;
  OldEsp := C.Esp;

  // Mess... apparently sometimes it does still execute the API before hitting the HWBP
  WriteProcessMemory(FDebugger.FProcess.hProcess, Pointer(OldEsp), @NullBytes, 32, Written);

  if not SetThreadContext(FTraceThread, C) then
    RaiseLastOSError;

  ResumeThread(FTraceThread);

  WaitForSingleObject(FDebugger.FProcRevealEvent, INFINITE);

  C.ContextFlags := CONTEXT_CONTROL;
  if not GetThreadContext(FTraceThread, C) then
    RaiseLastOSError;

  Result := NativeUInt(FDebugger.FProcAddr);

  C.Esp := OldEsp;
  if not SetThreadContext(FTraceThread, C) then
    RaiseLastOSError;
end;

procedure TASTracer.Log(MsgType: TLogMsgType; const Msg: string);
begin
  Synchronize(procedure begin
    FDebugger.Log(MsgType, Msg);
  end);
end;

end.
