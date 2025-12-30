unit ASProtect;

interface

uses Windows, Classes, DebuggerCore, SysUtils, Generics.Collections, Utils, RolyPoly, AIP;

type
  TASDebugger = class(TDebuggerCore)
  private
    FBaseOfData: NativeUInt;
    FSizeOfImage: UInt32;
    FPESections: array of TImageSectionHeader;

    FAntiDebugEH: Pointer;
    FTextUnpackedAddr: NativeUInt;

    FGuardStart, FGuardEnd: NativeUInt;
    FGuardStepping: Boolean;
    FGuardAddrs: TList<NativeUInt>;

    FSiteTargetToSite: TDictionary<Pointer, Pointer>;

    FASRegion: TMemoryRegion; // Region to scan for proc reveal point
    FGetProcResultAddr, FProcTypeAddr, FGetProcResultAddrAIP, FProcTypeAddrAIP: NativeUInt; // API in eax
    FProcRevealEvent: THandle;
    FProcAddr: Pointer;
    FProcIsJmp, FAIPInPlay: Boolean;
    FAIP: TAIP;

    FRolyPoly: TRolyPoly;
    FPolyCode: TList<TFixedPolyCode>;

    FOEP: NativeUInt;

    procedure GetASRegion(Address: NativeUInt);

    function IsGuardedAddress(Address: NativeUInt): Boolean;
    function ProcessGuardedAccess(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal;
    procedure PlaceBPOnStolen(SiteAddr: NativeUInt);

    procedure FixupAPICallSites(hThread: THandle);
    procedure FinishUnpacking;

    procedure InitTracing;
  protected
    procedure OnDebugStart(var hPE: THandle); override;
    procedure OnHardwareBreakpoint(hThread: THandle; BPA: NativeUInt; var C: TContext); override;
    function OnSoftwareBreakpoint(hThread: THandle; BPA: Pointer): TSoftBPAction; override;
    procedure OnUnsolicitedSoftwareBreakpoint(hThread: THandle; BPA: Pointer); override;
    function OnAccessViolation(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal; override;
    function OnSinglestep(BPA: NativeUInt): Cardinal; override;
  public
    destructor Destroy; override;

    function StolenRegionAlreadyProcessed(AAddress: NativeUInt): Boolean;
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
  FSiteTargetToSite.Free;
  FAIP.Free;

  inherited;
end;

procedure TASDebugger.OnDebugStart(var hPE: THandle);
var
  Buf, BufAlloc: PByte;
  Sect: PImageSectionHeader;
  i: Integer;
  NumRead: Cardinal;
begin
  FSiteTargetToSite := TDictionary<Pointer, Pointer>.Create;
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
    FSizeOfImage := PImageNTHeaders(Buf).OptionalHeader.SizeOfImage;
  finally
    FreeMem(BufAlloc);
  end;

  FGuardAddrs := TList<NativeUInt>.Create;
  // 1020 because 1000 has some extra code shuffling going on...
  SetBreakpoint(FImageBase + $1020, hwWrite);
end;

procedure TASDebugger.GetASRegion(Address: NativeUInt);
var
  i: Integer;
begin
  FetchMemoryRegions;

  for i := 0 to High(FMemRegions) do
    if FMemRegions[i].Contains(Address) then
    begin
      FASRegion := FMemRegions[i];
      Break;
    end;

  Log(ltGood, Format('AS region: %X~%X', [FASRegion.Address, FASRegion.Address + FASRegion.Size]));
end;

procedure TASDebugger.OnHardwareBreakpoint(hThread: THandle; BPA: NativeUInt; var C: TContext);
const
  CALL = 0;
  JMP = 1;
var
  OpTypes: array[0..1] of Byte;
  RetAddr, OldProt: NativeUInt;
  Instr: Word;
begin
  if BPA = FImageBase + $1020 then
  begin
    Log(ltGood, 'Text accessed from ' + IntToHex(C.Eip, 8));
    RPM(C.Eip, @Instr, 2);
    if Instr <> $A5F3 then // rep movsd
      Exit;

    if FASRegion.Address = 0 then
      GetASRegion(C.Eip);

    // This access should be in a Move() call with two registers on the stack before ret.
    RPM(C.Esp + 8, @RetAddr, SizeOf(RetAddr));
    if not FASRegion.Contains(RetAddr) then
      raise Exception.Create('Unexpected stack layout');
    ResetBreakpoint(Pointer(BPA));
    SetBreakpoint(RetAddr);
    FTextUnpackedAddr := RetAddr;
  end
  else if BPA = FTextUnpackedAddr then
  begin
    ResetBreakpoint(Pointer(BPA));
    // Unpacking .text is done - detect further accesses on it for IAT/stolen code references.
    // Use READONLY for first hit because it still does quite a bit of reading beforehand...
    FGuardStart := FImageBase + FPESections[0].VirtualAddress;
    FGuardEnd := FImageBase + FBaseOfData;
    VirtualProtectEx(FProcess.hProcess, Pointer(FGuardStart), FGuardEnd - FGuardStart, PAGE_READONLY, OldProt);
  end
  else if (BPA = FGetProcResultAddr) or (BPA = FGetProcResultAddrAIP) then
  begin
    //Log(ltGood, Format('-> %X', [C.Eax]));
    FProcAddr := Pointer(C.Eax);
  end
  else if (BPA = FProcTypeAddr) or (BPA = FProcTypeAddrAIP) then
  begin
    SuspendThread(hThread);

    if BPA = FProcTypeAddr then
    begin
      // Many thanks to pstolarz for his extensive documentation
      // https://github.com/pstolarz/asprext/tree/master/analysis/1.6x/aip
      if not RPM(C.Eax + $4A, @OpTypes, 2) then
        raise Exception.Create('RPM for env failed');

      if (Byte(C.Edx) <> OpTypes[CALL]) and (Byte(C.Edx) <> OpTypes[JMP]) then
        raise Exception.Create('Op type fault');

      FProcIsJmp := Byte(C.Edx) = OpTypes[JMP];
      FAIPInPlay := False;

      if FProcIsJmp then
        Log(ltGood, Format('-> %p, jmp', [FProcAddr]))
      else
        Log(ltGood, Format('-> %p, call', [FProcAddr]));
    end
    else
    begin
      if FAIP = nil then
        FAIP := TAIP.Create(FProcess.hProcess, hThread, C.Eax, Log);

      FAIPInPlay := True;
    end;

    SetEvent(FProcRevealEvent);
  end;
end;

function TASDebugger.OnSinglestep(BPA: NativeUInt): Cardinal;
var
  OldProt: Cardinal;
begin
  if FGuardStepping then
  begin
    // Must be here because only now the offset has been written.
    if FGuardAddrs.Count >= 2 then
      if FGuardAddrs.Last = FGuardAddrs[FGuardAddrs.Count - 2] + 1 then
        PlaceBPOnStolen(FGuardAddrs.Last - 1);

    // Re-apply guard.
    VirtualProtectEx(FProcess.hProcess, Pointer(FGuardStart), FGuardEnd - FGuardStart, PAGE_NOACCESS, OldProt);
    FGuardStepping := False;
    Result := DBG_CONTINUE;
  end
  else
    Result := inherited;
end;

procedure TASDebugger.PlaceBPOnStolen(SiteAddr: NativeUInt);
var
  Site: array[0..4] of Byte;
  SiteTarget: Cardinal;
  mbi: TMemoryBasicInformation;
begin
  if not RPM(SiteAddr, @Site[0], 5) then
    Exit;

  if Site[0] = $E9 then
    SiteTarget := PCardinal(@Site[1])^ + SiteAddr + 5
  else if Site[0] = $68 then
    SiteTarget := PCardinal(@Site[1])^
  else
    Exit;

  if (SiteTarget >= FImageBase) and (SiteTarget < FImageBase + FSizeOfImage) then
    Exit;
  if (VirtualQueryEx(FProcess.hProcess, Pointer(SiteTarget), mbi, SizeOf(mbi)) = 0) or (mbi.State <> MEM_COMMIT) then
    Exit;

  // Set a breakpoint in case this stolen code is a stolen OEP.
  Log(ltInfo, Format('Set soft bp on %X', [SiteTarget]));
  SetSoftBP(Pointer(SiteTarget));

  FSiteTargetToSite.AddOrSetValue(Pointer(SiteTarget), Pointer(SiteAddr));
end;

function TASDebugger.OnSoftwareBreakpoint(hThread: THandle; BPA: Pointer): TSoftBPAction;
var
  Site: Pointer;
  x, CAddr: NativeUInt;
  C: TContext;
begin
  Result := sbpClearContinue;
  Log(ltInfo, Format('Soft BP at 0x%p', [BPA]));

  if BPA = FAntiDebugEH then
  begin
    // eax holds a CONTEXT where DR was cleared.
    C.ContextFlags := CONTEXT_INTEGER;
    GetThreadContext(hThread, C);
    CAddr := C.Eax;
    RPM(CAddr, @C, SizeOf(C));
    ApplyDebugRegisters(C);
    WriteProcessMemory(FProcess.hProcess, Pointer(CAddr), @C, SizeOf(C), x);
    Exit; // sbpClear is fine; this is actually called a second time, but we're done with hwbps by then.
  end;

  // ASProtect jumps straight to the stolen code, it doesn't execute the jmp in the text section.
  // That's why we have to jump through these breakpoints hoops, but we can look up the text location here.
  if not FSiteTargetToSite.TryGetValue(BPA, Site) then
    raise Exception.Create('Address not found in dict');

  Log(ltGood, Format('OEP (stolen!): 0x%p', [Site]));
  FOEP := NativeUInt(Site);

  VirtualProtectEx(FProcess.hProcess, Pointer(FGuardStart), FGuardEnd - FGuardStart, PAGE_EXECUTE_READ, x);

  if FGuardAddrs.Count > 0 then
    FixupAPICallSites(hThread)
  else
    FinishUnpacking;
end;

procedure TASDebugger.OnUnsolicitedSoftwareBreakpoint(hThread: THandle; BPA: Pointer);
var
  tbi: TThreadBasicInformation;
  SEHHead, ExcHandler: PByte;
  nRead: NativeUInt;
  Instr: Word;
begin
  inherited;

  // Note: This seems to be an optional ASProtect setting, some targets don't do it.

  if FASRegion.Address <> 0 then
    Exit;

  GetASRegion(NativeUInt(BPA));

  // Fetch the current SEH code pointer.
  if NtQueryInformationThread(hThread, 0 {ThreadBasicInformation}, @tbi, SizeOf(tbi), nil) <> 0 then
    Exit;
  if not ReadProcessMemory(FProcess.hProcess, tbi.TebBaseAddress, @SEHHead, 4, nRead) then
    Exit;
  if not ReadProcessMemory(FProcess.hProcess, SEHHead + 4, @ExcHandler, 4, nRead) then
    Exit;

  Log(ltInfo, Format('EH: %p', [ExcHandler]));

  // This is a function that sets DRs to 0 in a CONTEXT. We set a swbp on it and restore the context.
  if ReadProcessMemory(FProcess.hProcess, ExcHandler + $3E, @Instr, 2, nRead) then
    if Instr = $C033 then  // xor eax, eax
    begin
      FAntiDebugEH := ExcHandler + $3E;
      SetSoftBP(FAntiDebugEH);
    end;
end;

function TASDebugger.OnAccessViolation(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal;
begin
  if FRolyPoly <> nil then
    Exit(FRolyPoly.OnAccessViolation(hThread, ExcRecord));
  if FAIP <> nil then
    Exit(FAIP.OnAccessViolation(hThread, ExcRecord));

  if FGetProcResultAddr <> 0 then
  begin
    // At this point, any exception is real (i.e., a bug).
    inherited;
    WaitForSingleObject(Handle, INFINITE);
  end;

  if not IsGuardedAddress(ExcRecord.ExceptionInformation[1]) then
  begin
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
begin
  Log(ltInfo, Format('[Guard] %X', [ExcRecord.ExceptionInformation[1]]));

  VirtualProtectEx(FProcess.hProcess, Pointer(FGuardStart), FGuardEnd - FGuardStart, PAGE_EXECUTE_READWRITE, OldProt);

  if NativeUInt(ExcRecord.ExceptionAddress) > FGuardEnd then
  begin
    FGuardAddrs.Add(ExcRecord.ExceptionInformation[1]);

    if FGuardAddrs.Count > 1000 then
      raise Exception.Create('Fast-fail: Something is wrong with page guarding in this target.');

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
    FOEP := NativeUInt(ExcRecord.ExceptionAddress);

    VirtualProtectEx(FProcess.hProcess, Pointer(FGuardStart), FGuardEnd - FGuardStart, PAGE_EXECUTE_READ, OldProt);

    if FGuardAddrs.Count > 0 then
      FixupAPICallSites(hThread)
    else
      FinishUnpacking;
  end;

  Result := DBG_CONTINUE;
end;

function TASDebugger.StolenRegionAlreadyProcessed(AAddress: NativeUInt): Boolean;
var
  C: TFixedPolyCode;
begin
  for C in FPolyCode do
    if C.OriginalExtent.Contains(AAddress) then
      Exit(True);
  Result := False;
end;

procedure TASDebugger.FixupAPICallSites(hThread: THandle);
begin
  SoftBPClear;
  InitTracing;

  SuspendThread(hThread);

  ResetBreakpoint(Pointer(FImageBase + $1000));
  SetBreakpoint(FGetProcResultAddr);
  SetBreakpoint(FProcTypeAddr);
  SetBreakpoint(FGetProcResultAddrAIP);
  SetBreakpoint(FProcTypeAddrAIP);

  Log(ltInfo, 'Begin tracing...');

  FProcRevealEvent := CreateEvent(nil, False, False, nil);

  TASTracer.Create(Self, hThread);
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

    FGetProcResultAddrAIP := FindDynamic('668B4DE08BD78B45F4E8????????8945FC', ASData, FASRegion.Size);
    if FGetProcResultAddrAIP = 0 then
      raise Exception.Create('Failed to find proc reveal point AIP');

    FProcTypeAddrAIP := FindDynamic('8A404A3A45EF0F85', ASData + FGetProcResultAddrAIP + 14, FASRegion.Size - FGetProcResultAddrAIP - 14);
    if FProcTypeAddrAIP = 0 then
      raise Exception.Create('Failed to find ref type AIP');

    Inc(FProcTypeAddrAIP, FASRegion.Address + FGetProcResultAddrAIP + 14);
    Inc(FGetProcResultAddrAIP, FASRegion.Address + 14);

    Log(ltGood, 'GetProcResultAddr: ' + IntToHex(FGetProcResultAddr, 8));
    Log(ltGood, 'ProcTypeAddr: ' + IntToHex(FProcTypeAddr, 8));
    Log(ltGood, 'GetProcResultAddrAIP: ' + IntToHex(FGetProcResultAddrAIP, 8));
    Log(ltGood, 'ProcTypeAddrAIP: ' + IntToHex(FProcTypeAddrAIP, 8));
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

      if FDebugger.StolenRegionAlreadyProcessed(SiteTarget) then
      begin
        Log(ltInfo, '(skipping, part of previous)');
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

  if FDebugger.FAIPInPlay then
    FDebugger.FAIP.ProcessImport(Address, FDebugger.FProcIsJmp);
end;

procedure TASTracer.Log(MsgType: TLogMsgType; const Msg: string);
begin
  Synchronize(procedure begin
    FDebugger.Log(MsgType, Msg);
  end);
end;

end.
