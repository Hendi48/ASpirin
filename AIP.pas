unit AIP;

// Handles 'Advanced Import Protection', where sometimes instructions directly after
// the API references are stolen and emulated by ASProtect.

// Based on research by Piotr Stolarz: https://github.com/pstolarz/asprext/blob/master/analysis/1.6x/aip/note-aip-emul

interface

uses Windows, SysUtils, Utils, Generics.Collections;

type
  TASAIPHandler = (phOffset, phRefType, phEmulId, ph3, ph4,
                   phImpSpec1, phImpSpec1b, phLibId, phProcId, phIsSipPatch,
                   eh0 = 0, ehOpcode = 1, ehPatchSize, ehAddrRVA, ehBranchType,
                   ehReg1, ehReg2, ehImm1, ehImm2, ehAddressingMode);
  TASAIPHandlerRec = record
    P: Pointer;
    Unk4: UInt32;
    Unk8: UInt32;
  end;
  TASAIPOpcode = (opcCall, opcJmp, opcCmpJcc, opcCmp, opcInvalid, opcAdd, opcMovRR, opcMovMR, opcMovRDR);
  TASAIPContext = record
    ClassInfo: Pointer;
    Unk4: Pointer;
    Unk8: Pointer;
    UnkC: Pointer;
    MemIndxs: Pointer;
    ImageBase: UInt32;
    PatchesCount: UInt32;
    EmulsCount: UInt32;
    ProtType: Byte;
    TextBase: UInt32;
    TextEndRVA: UInt32;
    { $2C }AIPEnterHandler: Pointer; // Where every import call site jumps to.
    { $30 }AIPExitHandler: Pointer;
    { $34 }Unk34Handler: Pointer;
    { $38 }Unk38Handler: Pointer;
    Imports: Pointer;
    Permut: array[TASAIPHandler] of Byte;
    OpcodePermut: array[TASAIPOpcode] of Byte;
    Patches: Pointer; // Pointer to array[PatchesCount] of entries.
    Emuls: Pointer; // Pointer to array[EmulsCount] of entries.
    Permut2: array[TASAIPHandler] of Byte; // Same stuff again?
    EntryAccessFuncs: array[0..9] of TASAIPHandlerRec; // Indexed by Permut[].
    ObfusKey: UInt32;
    EntrySize: UInt32;
  end;
  {$IF SIZEOF(TASAIPContext) <> $E8}
    {$MESSAGE ERROR 'Alignment mismatch!'}
  {$IFEND}

  TAIPEntryOffsets = record
    Offsets: array[TASAIPHandler] of Integer;
    Key: UInt32;

    function GetByte(E: Pointer; Typ: TASAIPHandler): Byte;
    function GetDword(E: Pointer; Typ: TASAIPHandler): UInt32;
    function GetDwordDeobfus(E: Pointer; Typ: TASAIPHandler): UInt32;
  end;

  TAIPPatch = record
    IsJmp: Boolean;
    EmulData: TBytes;
  end;

  TAIP = class
  type
    TState = (aipInit, aipTracing, aipReady);
  private
    FProcess, FTraceThread: THandle;
    FContext: TASAIPContext;
    FEntryOffsets: TAIPEntryOffsets;
    FPatches: TDictionary<NativeUInt, TAIPPatch>;
    FState: TState;

    FBaitPage: Pointer;
    FBaitAccessOffset: Integer;
    FTraceSignal: THandle;

    Log: TLogProc;

    procedure TraceAccessFuncs;
    procedure FetchEntries;
    procedure RestoreEmulatedCode(ToAddress: NativeUInt; const EmulEntry: TBytes);

    function RecoverCmp(const E: TBytes): TBytes;
    function RecoverCmpJcc(const E: TBytes; ToAddress: NativeUInt): TBytes;
    function RecoverAdd(const E: TBytes): TBytes;
    function RecoverMovRR(const E: TBytes): TBytes;
    function RecoverMovMR(const E: TBytes; Space: Integer): TBytes;
  public
    constructor Create(hProcess, hTraceThread: THandle; AContextAddr: NativeUInt; ALogProc: TLogProc);
    destructor Destroy; override;

    function OnAccessViolation(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal;

    procedure ProcessImport(RefAddr: NativeUInt; out RefIsJmp: Boolean; var ProcAddr: Pointer; ProcAddrIsObfus: Boolean);
  end;

implementation

uses TypInfo;

procedure DecodeEmulEntry(var E: TBytes; ObfusKey: UInt32);
var
  i: Integer;
  Key: array[0..15] of Byte;
begin
  PCardinal(@Key[0])^ := ObfusKey;
  for i := 4 to High(Key) do
    Key[i] := i + 1;

  for i := 0 to High(E) do
    E[i] := E[i] xor Key[i mod Length(Key)];
end;

{ TAIP }

constructor TAIP.Create(hProcess, hTraceThread: THandle; AContextAddr: NativeUInt; ALogProc: TLogProc);
var
  nRead: NativeUInt;
begin
  FProcess := hProcess;
  FTraceThread := hTraceThread;
  Log := ALogProc;

  FPatches := TDictionary<NativeUInt, TAIPPatch>.Create;

  if not ReadProcessMemory(hProcess, Pointer(AContextAddr), @FContext, SizeOf(FContext), nRead) then
    raise Exception.Create('Reading context failed');

  FBaitPage := VirtualAllocEx(hProcess, nil, $1000,  MEM_COMMIT or MEM_RESERVE, PAGE_NOACCESS);
  if FBaitPage = nil then
    raise Exception.Create('BaitPage allocation failed');

  FTraceSignal := CreateEvent(nil, False, False, nil);
end;

destructor TAIP.Destroy;
begin
  FPatches.Free;
  CloseHandle(FTraceSignal);

  inherited;
end;

procedure TAIP.ProcessImport(RefAddr: NativeUInt; out RefIsJmp: Boolean; var ProcAddr: Pointer; ProcAddrIsObfus: Boolean);
var
  P: TAIPPatch;
begin
  if FState = aipInit then
  begin
    TraceAccessFuncs;
    FetchEntries;
    FState := aipReady;
  end;

  if not FPatches.TryGetValue(RefAddr, P) then
    raise Exception.Create('AIP entry not found');

  RefIsJmp := P.IsJmp;
  if P.EmulData <> nil then
    RestoreEmulatedCode(RefAddr + 6, P.EmulData);

  if ProcAddrIsObfus then
    ProcAddr := Pointer(NativeUInt(ProcAddr) + FContext.ObfusKey);
end;

const
  BAIT_RET_OFFSET = $F00;

function TAIP.OnAccessViolation(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal;
begin
  Log(ltInfo, '[AIP] AV at ' + IntToHex(UIntPtr(ExcRecord.ExceptionAddress)));
  SuspendThread(hThread);

  if FState = aipTracing then
  begin
    if UIntPtr(ExcRecord.ExceptionAddress) = UIntPtr(FBaitPage) + BAIT_RET_OFFSET then
      raise Exception.Create('Accessor function returned unexpectedly');
    if (ExcRecord.ExceptionInformation[1] and $FFFFF000) <> UIntPtr(FBaitPage) then
      raise Exception.Create('Access trace AV not due to bait');

    FBaitAccessOffset := ExcRecord.ExceptionInformation[1] - UIntPtr(FBaitPage);
    SetEvent(FTraceSignal);
  end;

  Result := DBG_CONTINUE;
end;

procedure TAIP.TraceAccessFuncs;
var
  C: TContext;
  i: TASAIPHandler;
  Ret: NativeUInt;
  nWritten: NativeUInt;
begin
  FState := aipTracing;
  // We will call each entry accessor function and present it with a NOACCESS page.
  // The resulting access violation will tell us what the function tried to read.
  for i := Low(FContext.Permut) to High(FContext.Permut) do
  begin
    C.ContextFlags := CONTEXT_CONTROL or CONTEXT_INTEGER;
    if not GetThreadContext(FTraceThread, C) then
      RaiseLastOSError;

    C.Eax := UIntPtr(FBaitPage); // Will be dereferenced by the function.
    C.Eip := UIntPtr(FContext.EntryAccessFuncs[FContext.Permut[i]].P);
    // Put a fail-safe return address.
    Ret := UIntPtr(FBaitPage) + BAIT_RET_OFFSET;
    WriteProcessMemory(FProcess, Pointer(C.Esp), @Ret, SizeOf(Ret), nWritten);

    if not SetThreadContext(FTraceThread, C) then
      RaiseLastOSError;

    ResumeThread(FTraceThread);

    if WaitForSingleObject(FTraceSignal, 10000) = WAIT_TIMEOUT then
      raise Exception.CreateFmt('Trace timed out for func %p', [FContext.EntryAccessFuncs[FContext.Permut[i]].P]);

    FEntryOffsets.Offsets[i] := FBaitAccessOffset;
    //Log(ltInfo, Format('%s -> %d', [GetEnumName(TypeInfo(TASPolyHandler), Ord(i)), FBaitAccessOffset]));
  end;
  FEntryOffsets.Key := FContext.ObfusKey;
end;

procedure TAIP.FetchEntries;
var
  i, EmulId: Cardinal;
  Data, Cursor: PByte;
  nRead: NativeUInt;
  P: TAIPPatch;
begin
  if FContext.PatchesCount = 0 then
    raise Exception.Create('No AIP patches?!');

  GetMem(Data, FContext.PatchesCount * FContext.EntrySize);
  try
    if not ReadProcessMemory(FProcess, FContext.Patches, Data, FContext.PatchesCount * FContext.EntrySize, nRead) then
      raise Exception.Create('Error reading patches');

    Cursor := Data;
    for i := 0 to FContext.PatchesCount - 1 do
    begin
      P.EmulData := nil;
      P.IsJmp := FEntryOffsets.GetByte(Cursor, phRefType) = FContext.OpcodePermut[opcJmp];

      EmulId := FEntryOffsets.GetDwordDeobfus(Cursor, phEmulId);
      if EmulId <> $FFFFFFFF then
      begin
        SetLength(P.EmulData, FContext.EntrySize);
        if not ReadProcessMemory(FProcess, PByte(FContext.Emuls) + EmulId * FContext.EntrySize, @P.EmulData[0], FContext.EntrySize, nRead) then
          raise Exception.Create('Error reading emul data');

        DecodeEmulEntry(P.EmulData, FContext.ObfusKey);
      end;

      FPatches.Add(FEntryOffsets.GetDwordDeobfus(Cursor, phOffset) + FContext.TextBase, P);
      Inc(Cursor, FContext.EntrySize);
    end;
  finally
    FreeMem(Data);
  end;
end;

procedure TAIP.RestoreEmulatedCode(ToAddress: NativeUInt; const EmulEntry: TBytes);
var
  CodedOpc: Byte;
  Opc: TASAIPOpcode;
  Code: TBytes;
  AvailSpace: Integer;
  nWritten: NativeUInt;
begin
  CodedOpc := FEntryOffsets.GetByte(@EmulEntry[0], ehOpcode);
  AvailSpace := FEntryOffsets.GetDwordDeobfus(@EmulEntry[0], ehPatchSize) - 6;

  Code := nil;
  for Opc := Low(TASAIPOpcode) to High(TASAIPOpcode) do
    if CodedOpc = FContext.OpcodePermut[Opc] then
    begin
      case Opc of
        //opcCall: ;
        //opcJmp: ;
        opcCmpJcc: Code := RecoverCmpJcc(EmulEntry, ToAddress);
        opcCmp: Code := RecoverCmp(EmulEntry);
        opcAdd: Code := RecoverAdd(EmulEntry);
        opcMovRR: Code := RecoverMovRR(EmulEntry);
        opcMovMR: Code := RecoverMovMR(EmulEntry, AvailSpace);
        //opcMovRDR: ;
        else raise Exception.CreateFmt('[AIP] Unimplemented opcode type: %s', [GetEnumName(TypeInfo(TASAIPOpcode), Ord(Opc))]);
      end;
      Break;
    end;

  if Code <> nil then
  begin
    if AvailSpace = Length(Code) then
    begin
      WriteProcessMemory(FProcess, Pointer(ToAddress), @Code[0], Length(Code), nWritten);
      Log(ltGood, Format('[AIP] Recovered stolen opcode of type %s', [GetEnumName(TypeInfo(TASAIPOpcode), Ord(Opc))]));
    end
    else
      raise Exception.CreateFmt('Recovered %d bytes, but space is %d (%s)', [Length(Code), AvailSpace, GetEnumName(TypeInfo(TASAIPOpcode), Ord(Opc))]);
  end;
end;

function TAIP.RecoverCmp(const E: TBytes): TBytes;
var
  R1, R2: Byte;
  D1, D2: UInt32;
  AddrMode: Byte;
begin
  R1 := FEntryOffsets.GetByte(@E[0], ehReg1);
  R2 := FEntryOffsets.GetByte(@E[0], ehReg2);
  D1 := FEntryOffsets.GetDword(@E[0], ehImm1);
  D2 := FEntryOffsets.GetDword(@E[0], ehImm2);
  AddrMode := FEntryOffsets.GetByte(@E[0], ehAddressingMode) - 2;

  if (R1 in [4, 5]) or (R2 in [4, 5]) then // These would have to be assembled differently (SIB/displ)
    raise Exception.Create('Unsupported reg encoding (esp/ebp)');

  if R1 > 7 then
    raise Exception.CreateFmt('Invalid reg byte: %d, %d', [R1, R2]);

  if (D1 <> 0) and (AddrMode = 0) then
    Inc(D1, FContext.ImageBase);
  if (D2 <> 0) and (AddrMode = 1) then
    Inc(D2, FContext.ImageBase);

  if R2 <= 7 then
  begin
    if (D1 <> 0) or (D2 <> 0) then
      raise Exception.Create('CmpDispl is currently not supported');

    case AddrMode of
      // cmp dword ptr [R1], R2
      0: Result := [$39, (R2 shl 3) or R1];
      // cmp R1, dword ptr [R2]
      1: Result := [$3B, (R1 shl 3) or R2];
      // cmp byte ptr [R1], R2
      2: Result := [$38, (R2 shl 3) or R1];
      // cmp R1, byte ptr [R2]
      3: Result := [$3A, (R1 shl 3) or R2];
      // cmp R1, R2
      4: Result := [$3B, $C0 or (R1 shl 3) or R2];
      else raise Exception.CreateFmt('Invalid cmp modifier: %d', [AddrMode]);
    end;
  end
  else
  begin
    if D1 <> 0 then
      raise Exception.Create('CmpDispl1 is currently not supported');

    case FEntryOffsets.GetByte(@E[0], ehAddressingMode) of
      // cmp dword ptr [R1], D2
      0: if D2 < $80 then Result := [$83, $38 + R1, D2] else Result := [$81, $38 + R1];
      // cmp byte ptr [R1], D2
      2: Result := [$80, $38 + R1, D2];
      // cmp R1, D2
      4: if D2 < $80 then Result := [$83, $F8 + R1, D2] else Result := [$81, $F8 + R1];
      else raise Exception.CreateFmt('Unsupported cmp modifier: %d', [AddrMode]);
    end;
    if Length(Result) = 2 then // put imm32
    begin
      SetLength(Result, 6);
      PCardinal(@Result[2])^ := D2;
    end;
  end;
end;

function TAIP.RecoverCmpJcc(const E: TBytes; ToAddress: NativeUInt): TBytes;
var
  Target: NativeUInt;
  Delta, L: Integer;
begin
  Result := RecoverCmp(E);
  L := Length(Result);

  Target := FEntryOffsets.GetDwordDeobfus(@E[0], ehAddrRVA) + FContext.ImageBase;
  Delta := Target - (ToAddress + Cardinal(L));
  if (Delta < -$7E) or (Delta > $81) then
  begin
    SetLength(Result, L + 6);
    Result[L] := $0F;
    Result[L+1] := $80 + FEntryOffsets.GetByte(@E[0], ehBranchType);
    PInteger(@Result[L+2])^ := Delta - 6;
  end
  else
  begin
    SetLength(Result, L + 2);
    Result[L] := $70 + FEntryOffsets.GetByte(@E[0], ehBranchType);
    Result[L+1] := Delta - 2;
  end;
end;

function TAIP.RecoverAdd(const E: TBytes): TBytes;
var
  Reg: Byte;
  Imm: UInt32;
  ByteImm: Boolean;
begin
  // add Reg, Imm
  Reg := FEntryOffsets.GetByte(@E[0], ehReg1);
  Imm := FEntryOffsets.GetDword(@E[0], ehImm1);

  ByteImm := (Imm < $80) or (Imm >= $FFFFFF80);

  if (Reg = 0) and not ByteImm then
    Result := [$05, 0,0,0,0] // Special eax case
  else if ByteImm then
  begin
    Result := [$83, $C0 or Reg, Byte(Imm)];
    Exit;
  end
  else
    Result := [$81, $C0 or Reg, 0,0,0,0];

  PCardinal(@Result[Length(Result) - 4])^ := Imm;
end;

function TAIP.RecoverMovRR(const E: TBytes): TBytes;
var
  R1, R2: Byte;
begin
  // mov R1, R2
  R1 := FEntryOffsets.GetByte(@E[0], ehReg1);
  R2 := FEntryOffsets.GetByte(@E[0], ehReg2);

  Result := [$8B, $C0 or (R1 shl 3) or R2];
end;

function TAIP.RecoverMovMR(const E: TBytes; Space: Integer): TBytes;
var
  Reg: Byte;
  Displ: UInt32;
begin
  // mov [Displ], Reg
  Reg := FEntryOffsets.GetByte(@E[0], ehReg1);
  Displ := FEntryOffsets.GetDword(@E[0], ehImm1) + FContext.ImageBase;

  if Space >= 7 then
    Result := [$89, $04 or (Reg shl 3), $25, 0,0,0,0]
  else
    Result := [$89, $05 or (Reg shl 3), 0,0,0,0];

  PCardinal(@Result[Length(Result) - 4])^ := Displ;
end;

{ TAIPEntryOffsets }

function TAIPEntryOffsets.GetByte(E: Pointer; Typ: TASAIPHandler): Byte;
begin
  Result := (PByte(E) + Offsets[Typ])^;
end;

function TAIPEntryOffsets.GetDword(E: Pointer; Typ: TASAIPHandler): UInt32;
begin
  Result := PCardinal(PByte(E) + Offsets[Typ])^;
end;

function TAIPEntryOffsets.GetDwordDeobfus(E: Pointer; Typ: TASAIPHandler): UInt32;
begin
  Result := PCardinal(PByte(E) + Offsets[Typ])^ + Key;
end;

end.
