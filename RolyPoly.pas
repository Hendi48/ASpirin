unit RolyPoly;

// Roly-Poly is hard at work recovering control flow in obfuscated code!

interface

uses Windows, SysUtils, BeaEngineDelphi32, Utils, Generics.Collections;

type
  TPolyDisassemblyState = (dsFlowObfusHit, dsComplete);

  TASPolyHandler = (phOffset, phFlowType, phTarget2, phTarget, phBranchType,
                    phCmpReg1, phCmpReg2, phCmpDispl1, phCmpDispl2, phCmpModifier);
  TASPolyContext = record
    ClassInfo: Pointer;
    Unk4: Pointer;
    Unk8: Pointer;
    UnkC: Pointer;
    ImageBase: Pointer;
    EntryCount: UInt32;
    PolyCodePtr: Pointer; // Pointer to the base of the actual obfuscated code.
    FlowObfusEnterHandler: Pointer; // Code that pushes processor state and enters ASPR DLL.
    FlowObfusExitHandler: Pointer; // Code that restores processor state and returns.
    Permut: array[TASPolyHandler] of Byte;
    EntriesPointer: Pointer; // Pointer to array[EntryCount] of entries.
    Permut2: array[TASPolyHandler] of Byte; // Same stuff again?
    EntryAccessFuncs: array[0..9] of Pointer; // Indexed by Permut[].
    ObfusKey: UInt32;
    EntrySize: UInt32;
  end;
  {$IF SIZEOF(TASPolyContext) <> $70}
    {$MESSAGE ERROR 'Alignment mismatch!'}
  {$IFEND}

  // These are obtained by calling&instrumenting each EntryAccessFunc.
  TEntryOffsets = record
    Offsets: array[TASPolyHandler] of Integer;
    Key: UInt32;

    function GetEntryOffset(E: Pointer): UInt32;
    function GetFlowType(E: Pointer): Byte;
    function GetTarget2(E: Pointer): Integer;
    function GetTarget(E: Pointer): Integer;
    function GetBranchType(E: Pointer): Byte;
    function GetCmpReg1(E: Pointer): Byte;
    function GetCmpReg2(E: Pointer): Byte;
    function GetCmpDispl1(E: Pointer): Integer;
    function GetCmpDispl2(E: Pointer): Integer;
    function GetCmpModifier(E: Pointer): Byte;
  end;

  TInstrDescr = record
    Opcode: TBytes;
    AbsTarget: UInt32; // relative to TRolyPoly.FAddress
    Origin: NativeUInt; // key to TRolyPoly.FDisassembly
  end;

  TFixedPolyCode = class
  public
    CodeBytes: TBytes;
    Fixups: TList<Integer>; // List of offsets for call REL32s that need to be adjusted later.
    Origin: NativeUInt; // Where we need to put the jump into the poly section.
    OriginalExtent: TMemoryRegion;

    constructor Create(const AOriginalExtent: TMemoryRegion);
    destructor Destroy; override;
  end;

  TRolyPolyState = (psInit, psTraceObfusEnter, psTraceAccessFunc, psEvalEntries);

  TRolyPoly = class
  private
    FProcess, FTraceThread: THandle;
    FAddress: NativeUInt; // Start address of polymorphically obfuscated function.
    FASRegion: TMemoryRegion; // Region of ASProtect DLL.
    FOriginalExtent: TMemoryRegion;
    FCodeDump: PByte;
    FCodeSize: NativeUInt;
    FDisassembly: TDictionary<NativeUInt, PDisasm>;
    FWorklist: TList<NativeUInt>;
    FNewInstrs: TList<TInstrDescr>;

    FState: TRolyPolyState;
    FStateSignal: THandle;

    FFlowObfusSite: NativeUInt;
    FFlowObfusEnter: NativeUInt;
    FPolyContext: TASPolyContext;
    FEntryOffsets: TEntryOffsets;
    FEntries: TDictionary<Integer, Pointer>;

    FBaitPage: Pointer;
    FBaitAccessOffset: Integer;

    Log: TLogProc;

    function DisassembleMore(AAddress: NativeUInt): TPolyDisassemblyState;
    procedure StartTrace(AAddress: NativeUInt);
    procedure TraceAccessFuncs;
    procedure FetchEntries;
    procedure ProcessFlowObfusEntry(E: Pointer);
    procedure ProcessNewInstrs;
    procedure CleanupCodeDump;

    procedure RecoverCall(E: Pointer);
    procedure RecoverJmp(E: Pointer);
    procedure RecoverJcc(E: Pointer; FromCmp: Boolean = False);
    procedure RecoverCmpJcc(E: Pointer);
  public
    constructor Create(hProcess, hTraceThread: THandle; AAddress: NativeUInt;
      AASRegion: TMemoryRegion; ALogProc: TLogProc);
    destructor Destroy; override;

    function OnAccessViolation(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal;

    function Run: TFixedPolyCode;
  end;

implementation

uses TypInfo;

{ TRolyPoly }

constructor TRolyPoly.Create(hProcess, hTraceThread: THandle; AAddress: NativeUInt;
  AASRegion: TMemoryRegion; ALogProc: TLogProc);
begin
  FProcess := hProcess;
  FTraceThread := hTraceThread;
  FAddress := AAddress;
  FASRegion := AASRegion;
  Log := ALogProc;

  FDisassembly := TDictionary<NativeUInt, PDisasm>.Create;
  FWorklist := TList<NativeUInt>.Create;
  FEntries := TDictionary<Integer, Pointer>.Create;
  FNewInstrs := TList<TInstrDescr>.Create;

  FStateSignal := CreateEvent(nil, False, False, nil);
end;

destructor TRolyPoly.Destroy;
var
  D: PDisasm;
  E: Pointer;
begin
  if FCodeDump <> nil then
    FreeMem(FCodeDump);

  for D in FDisassembly.Values do
    Dispose(D);
  FDisassembly.Free;
  FWorklist.Free;
  for E in FEntries.Values do
    FreeMem(E);
  FEntries.Free;
  FNewInstrs.Free;

  CloseHandle(FStateSignal);

  inherited;
end;

function TRolyPoly.DisassembleMore(AAddress: NativeUInt): TPolyDisassemblyState;
var
  Dis: TDisasm;
  PD: PDisasm;
  Len: Integer;
begin
  FillChar(Dis, SizeOf(Dis), 0);
  Dis.VirtualAddr := AAddress;
  Dis.EIP := UIntPtr(FCodeDump + AAddress - FAddress);
  Dis.Options := BeaEngineDelphi32.Tabulation;
  Dis.Archi := 32;

  while True do
  begin
    if FDisassembly.ContainsKey(Dis.VirtualAddr) then
      Exit(dsComplete);

    Len := Disasm(Dis);
    if Len = UNKNOWN_OPCODE then
      raise Exception.CreateFmt('Disassembly ran into unknown opcode at %X', [Dis.VirtualAddr]);

    Dis.Reserved_[0] := Len; // It's awkward that BeaEngine doesn't otherwise store this...

    New(PD);
    PD^ := Dis;
    FDisassembly.Add(PD.VirtualAddr, PD);

    Dis.EIP := Dis.EIP + UIntPtr(Len);
    Dis.VirtualAddr := Dis.VirtualAddr + UIntPtr(Len);
    if (Byte(Dis.Instruction.Category) = CONTROL_TRANSFER) and (Dis.Instruction.Opcode <> $C9 {how is LEAVE a control transfer???}) then
    begin
      // ret?
      if (Dis.Instruction.Opcode = $C2) or (Dis.Instruction.Opcode = $C3) then
        Exit(dsComplete);

      // jmp?
      if (Dis.Instruction.Opcode = $E9) or (Dis.Instruction.Opcode = $EB) then
      begin
        Dis.VirtualAddr := Dis.Instruction.AddrValue;
        Dis.EIP := UIntPtr(FCodeDump + Dis.Instruction.AddrValue - FAddress);
        if (Dis.EIP < UIntPtr(FCodeDump)) or (Dis.EIP >= UIntPtr(FCodeDump) + FCodeSize) then
          raise Exception.CreateFmt('Attempted to jump out of bounds to %X', [Dis.VirtualAddr]);
        Continue;
      end;

      // call?
      if Dis.Instruction.Opcode = $E8 then
        if Dis.Instruction.AddrValue and $FFF = 0 then // these seem to always be on a page boundary?
        begin
          FFlowObfusSite := PD.VirtualAddr;
          FFlowObfusEnter := Dis.Instruction.AddrValue;
          Exit(dsFlowObfusHit);
        end
        else
          Continue;

      // call/jmp ptr?
      if Dis.Instruction.Opcode = $FF then
        if Dis.Instruction.BranchType = CallType then
          Continue
        else
          Exit(dsComplete);

      // jcc?
      FWorklist.Add(Dis.Instruction.AddrValue);
    end;
  end;
end;

const
  BAIT_RET_OFFSET = $F00;

function TRolyPoly.OnAccessViolation(hThread: THandle; const ExcRecord: TExceptionRecord): Cardinal;
var
  C: TContext;
  ObjPtr, nRead: NativeUInt;
  i: Integer;
begin
  Log(ltInfo, 'AV at ' + IntToHex(UIntPtr(ExcRecord.ExceptionAddress)));
  SuspendThread(hThread);

  if FState = psTraceObfusEnter then
  begin
    if not FASRegion.Contains(UIntPtr(ExcRecord.ExceptionAddress)) then
      raise Exception.Create('AV is at unexpected address');

    C.ContextFlags := CONTEXT_CONTROL;
    if not GetThreadContext(hThread, C) then
      raise Exception.Create('GetThreadContext failed');
    if not ReadProcessMemory(FProcess, Pointer(C.Esp + 4), @ObjPtr, 4, nRead) then
      raise Exception.CreateFmt('Failed to read dword at %X', [C.Esp + 4]);
    Log(ltInfo, 'Ctx at ' + IntToHex(ObjPtr));

    if not ReadProcessMemory(FProcess, Pointer(ObjPtr), @FPolyContext, SizeOf(FPolyContext), nRead) then
      raise Exception.CreateFmt('Failed to read object at %X', [ObjPtr]);

    // Do a sanity check on the function pointers to ensure the struct layout is as expected.
    if IntPtr(FPolyContext.EntryAccessFuncs[0]) < $10000 then
      raise Exception.CreateFmt('Pointer %p looks out of range - struct layout changed?', [FPolyContext.EntryAccessFuncs[0]]);
    for i := 1 to High(FPolyContext.EntryAccessFuncs) do
      if Abs(IntPtr(FPolyContext.EntryAccessFuncs[i]) - IntPtr(FPolyContext.EntryAccessFuncs[0])) > $10000 then
        raise Exception.CreateFmt('Struct sanity check failed at index %d', [i]);

    SetEvent(FStateSignal);
  end
  else if FState = psTraceAccessFunc then
  begin
    if UIntPtr(ExcRecord.ExceptionAddress) = UIntPtr(FBaitPage) + BAIT_RET_OFFSET then
      raise Exception.Create('Accessor function returned unexpectedly');
    if (ExcRecord.ExceptionInformation[1] and $FFFFF000) <> UIntPtr(FBaitPage) then
      raise Exception.Create('Access trace AV not due to bait');

    FBaitAccessOffset := ExcRecord.ExceptionInformation[1] - UIntPtr(FBaitPage);
    SetEvent(FStateSignal);
  end;

  Result := DBG_CONTINUE;
end;

function TRolyPoly.Run: TFixedPolyCode;
var
  ReadAddr, PageOffset, PageBase, nRead: NativeUInt;
  BufPtr: PByte;
  Item: NativeUInt;
  OldProt: Cardinal;
  E: Pointer;
  D: PDisasm;
begin
  PageBase := FAddress and not $FFF;
  PageOffset := FAddress - PageBase;
  ReadAddr := PageBase;

  while True do
  begin
    Inc(FCodeSize, $1000);
    ReallocMem(FCodeDump, FCodeSize);
    BufPtr := FCodeDump + FCodeSize - $1000;
    if not ReadProcessMemory(FProcess, Pointer(ReadAddr), BufPtr, $1000, nRead) then
      RaiseLastOSError;

    // Skip bytes before FAddress on first iteration
    if (ReadAddr = PageBase) and (PageOffset > 0) then
    begin
      Move(BufPtr[PageOffset], BufPtr[0], $1000 - PageOffset);
      Dec(FCodeSize, PageOffset);
      ReallocMem(FCodeDump, FCodeSize);
    end;

    if (FCodeSize >= 8) and (PUInt64(FCodeDump + FCodeSize - 8)^ = 0) then
      Break;

    Inc(ReadAddr, $1000);
  end;

  FOriginalExtent := TMemoryRegion.Create(FAddress, FCodeSize);

  FWorklist.Add(FAddress);

  while FWorklist.Count > 0 do
  begin
    Item := FWorklist[0];
    FWorklist.Delete(0);

    if DisassembleMore(Item) = dsFlowObfusHit then
    begin
      if (FState <> psEvalEntries) or (FFlowObfusEnter <> UIntPtr(FPolyContext.FlowObfusEnterHandler)) then
      begin
        FState := psTraceObfusEnter;
        VirtualProtectEx(FProcess, Pointer(FASRegion.Address), FASRegion.Size, PAGE_NOACCESS, OldProt);
        StartTrace(FFlowObfusEnter);
        if WaitForSingleObject(FStateSignal, 10000) = WAIT_TIMEOUT then
          raise Exception.Create('Trace timed out');

        TraceAccessFuncs;
        FetchEntries;
        FState := psEvalEntries;
      end;

      if not FEntries.TryGetValue(FFlowObfusSite - FAddress, E) then
        raise Exception.CreateFmt('No entry found for site %X', [FFlowObfusSite]);

      ProcessFlowObfusEntry(E);
    end;
  end;

  VirtualProtectEx(FProcess, Pointer(FASRegion.Address), FASRegion.Size, PAGE_EXECUTE_READWRITE, OldProt);

  CleanupCodeDump;
  ProcessNewInstrs;

  Result := TFixedPolyCode.Create(FOriginalExtent);
  for D in FDisassembly.Values do
    if (D^.Instruction.Opcode = $E8) and (PInteger(D^.EIP + 1)^ = -1) then
    begin
      PInteger(D^.EIP + 1)^ := D^.Instruction.AddrValue;
      Result.Fixups.Add(D^.VirtualAddr + 1 - FAddress);
    end;
  SetLength(Result.CodeBytes, FCodeSize);
  Move(FCodeDump^, Result.CodeBytes[0], FCodeSize);

  Log(ltGood, Format('Poly recovery done: %d bytes, %d fixups', [FCodeSize, Result.Fixups.Count]));
end;

procedure TRolyPoly.StartTrace(AAddress: NativeUInt);
var
  C: TContext;
begin
  Log(ltInfo, Format('Trace: %X', [AAddress]));

  C.ContextFlags := CONTEXT_CONTROL;
  if not GetThreadContext(FTraceThread, C) then
    RaiseLastOSError;

  C.Eip := AAddress;

  if not SetThreadContext(FTraceThread, C) then
    RaiseLastOSError;

  ResumeThread(FTraceThread);
end;

procedure TRolyPoly.TraceAccessFuncs;
var
  C: TContext;
  i: TASPolyHandler;
  Ret: NativeUInt;
  nWritten: NativeUInt;
begin
  if FBaitPage = nil then
    FBaitPage := VirtualAllocEx(FProcess, nil, $1000, MEM_COMMIT or MEM_RESERVE, PAGE_NOACCESS);

  // We will call each entry accessor function and present it with a NOACCESS page.
  // The resulting access violation will tell us what the function tried to read.
  FState := psTraceAccessFunc;
  for i := Low(FPolyContext.Permut) to High(FPolyContext.Permut) do
  begin
    C.ContextFlags := CONTEXT_CONTROL or CONTEXT_INTEGER;
    if not GetThreadContext(FTraceThread, C) then
      RaiseLastOSError;

    C.Eax := UIntPtr(FBaitPage); // Will be dereferenced by the function.
    C.Eip := UIntPtr(FPolyContext.EntryAccessFuncs[FPolyContext.Permut[i]]);
    // Put a fail-safe return address.
    Ret := UIntPtr(FBaitPage) + BAIT_RET_OFFSET;
    WriteProcessMemory(FProcess, Pointer(C.Esp), @Ret, SizeOf(Ret), nWritten);

    if not SetThreadContext(FTraceThread, C) then
      RaiseLastOSError;

    ResumeThread(FTraceThread);

    if WaitForSingleObject(FStateSignal, 10000) = WAIT_TIMEOUT then
      raise Exception.CreateFmt('Trace timed out for func %p', [FPolyContext.EntryAccessFuncs[FPolyContext.Permut[i]]]);

    FEntryOffsets.Offsets[i] := FBaitAccessOffset;
    Log(ltInfo, Format('%s -> %d', [GetEnumName(TypeInfo(TASPolyHandler), Ord(i)), FBaitAccessOffset]));
  end;
end;

procedure TRolyPoly.FetchEntries;
var
  EData, ECursor, E: PByte;
  nRead: NativeUInt;
  i: Integer;
begin
  FEntryOffsets.Key := FPolyContext.ObfusKey;

  GetMem(EData, FPolyContext.EntryCount * FPolyContext.EntrySize);
  try
    if not ReadProcessMemory(FProcess, FPolyContext.EntriesPointer, EData, FPolyContext.EntryCount * FPolyContext.EntrySize, nRead) then
      raise Exception.Create('Reading flow obfuscation entry data failed');

    ECursor := EData;
    for i := 0 to FPolyContext.EntryCount - 1 do
    begin
      GetMem(E, FPolyContext.EntrySize);
      Move(ECursor^, E^, FPolyContext.EntrySize);
      FEntries.Add(FEntryOffsets.GetEntryOffset(E), E);

      Inc(ECursor, FPolyContext.EntrySize);
    end;
  finally
    FreeMem(EData);
  end;
end;

procedure TRolyPoly.ProcessFlowObfusEntry(E: Pointer);
var
  FlowType: Byte;
begin
  FlowType := FEntryOffsets.GetFlowType(E);
  case FlowType of
    0: RecoverCall(E);
    1: RecoverJmp(E);
    2: RecoverJcc(E);
    3: RecoverCmpJcc(E);
    else raise Exception.CreateFmt('Invalid flow type %d', [FlowType]);
  end;
end;

procedure TRolyPoly.RecoverCall(E: Pointer);
var
  Origin, CallTarget, CallReturn: UInt32;
  PushAddr: NativeUInt;
begin
  Origin := FEntryOffsets.GetEntryOffset(E);
  CallTarget := FEntryOffsets.GetTarget(E);

  PushAddr := FAddress + Origin - 5;
  if not FDisassembly.ContainsKey(PushAddr) or (FDisassembly[PushAddr].Instruction.Opcode <> $68) then
    raise Exception.Create('Push belonging to call not found');

  CallReturn := FDisassembly[PushAddr].Instruction.Immediat - FAddress;

  if CallReturn > FCodeSize then
    raise Exception.CreateFmt('CallReturn seems out of bounds: %d', [CallReturn]);

  // Push becomes call
  with FDisassembly[PushAddr]^ do
  begin
    Instruction.Opcode := $E8;
    PByte(EIP)^ := $E8;
    if CallTarget <> $FFFFFFFF then
    begin
      Instruction.AddrValue := CallTarget; // used later
      PInteger(EIP + 1)^ := -1; // fixed up later
    end
    else // target inside stolen region
    begin
      CallTarget := FEntryOffsets.GetTarget2(E);
      if CallTarget > FCodeSize then
        raise Exception.Create('Call target out of bounds');
      Instruction.AddrValue := FAddress + CallTarget;
      PInteger(EIP + 1)^ := CallTarget - (Origin - 5) - 5;
      FWorklist.Add(CallTarget + FAddress);
    end;
  end;
  // Call becomes jmp
  with FDisassembly[PushAddr + 5]^ do
  begin
    Instruction.Opcode := $E9;
    Instruction.AddrValue := CallReturn + FAddress;
    PByte(EIP)^ := $E9;
    PInteger(EIP + 1)^ := CallReturn - Origin - 5;
  end;

  FWorklist.Add(CallReturn + FAddress);
end;

procedure TRolyPoly.RecoverJmp(E: Pointer);
var
  Origin, JmpTarget: UInt32;
begin
  Origin := FEntryOffsets.GetEntryOffset(E);
  JmpTarget := FEntryOffsets.GetTarget2(E);

  if JmpTarget > FCodeSize then
    raise Exception.CreateFmt('JmpTarget seems out of bounds: %d', [JmpTarget]);

  // Call becomes jmp
  with FDisassembly[FAddress + Origin]^ do
  begin
    Instruction.Opcode := $E9;
    Instruction.AddrValue := FAddress + JmpTarget;
    PByte(EIP)^ := $E9;
    PInteger(EIP + 1)^ := JmpTarget - Origin - 5;
  end;

  FWorklist.Add(JmpTarget + FAddress);
end;

procedure TRolyPoly.RecoverJcc(E: Pointer; FromCmp: Boolean);
var
  D1, D2: TInstrDescr;
begin
  // Jcc for 'true' path
  D1.Opcode := [$0F, $80 + FEntryOffsets.GetBranchType(E)];
  D1.AbsTarget := FEntryOffsets.GetTarget(E);
  if not FromCmp then
    D1.Origin := FEntryOffsets.GetEntryOffset(E) + FAddress
  else
    D1.Origin := 0;
  // Jmp for 'false' path
  D2.Opcode := [$E9];
  D2.AbsTarget := FEntryOffsets.GetTarget2(E);
  D2.Origin := 0;

  FNewInstrs.Add(D1);
  FNewInstrs.Add(D2);

  FWorklist.Add(D1.AbsTarget + FAddress);
  FWorklist.Add(D2.AbsTarget + FAddress);
end;

procedure TRolyPoly.RecoverCmpJcc(E: Pointer);
var
  R1, R2: Byte;
  D1, D2: UInt32;
  Cmp: TInstrDescr;
begin
  R1 := FEntryOffsets.GetCmpReg1(E);
  R2 := FEntryOffsets.GetCmpReg2(E);
  D1 := FEntryOffsets.GetCmpDispl1(E);
  D2 := FEntryOffsets.GetCmpDispl2(E);

  if (R1 in [4, 5]) or (R2 in [4, 5]) then // These would have to be assembled differently (SIB/displ)
    raise Exception.Create('Unsupported reg encoding (esp/ebp)');

  if R1 > 7 then
    raise Exception.CreateFmt('Invalid reg byte: %d, %d', [R1, R2]);

  if R2 <= 7 then
  begin
    if (D1 <> 0) or (D2 <> 0) then
      raise Exception.Create('CmpDispl is currently not supported');

    case FEntryOffsets.GetCmpModifier(E) of
      // cmp dword ptr [R1], R2
      0: Cmp.Opcode := [$39, (R2 shl 3) or R1];
      // cmp R1, dword ptr [R2]
      1: Cmp.Opcode := [$3B, (R1 shl 3) or R2];
      // cmp byte ptr [R1], R2
      2: Cmp.Opcode := [$38, (R2 shl 3) or R1];
      // cmp R1, byte ptr [R2]
      3: Cmp.Opcode := [$3A, (R1 shl 3) or R2];
      // cmp R1, R2
      4: Cmp.Opcode := [$3B, $C0 or (R1 shl 3) or R2];
      else raise Exception.CreateFmt('Invalid cmp modifier: %d', [FEntryOffsets.GetCmpModifier(E)]);
    end;
  end
  else
  begin
    if D1 <> 0 then
      raise Exception.Create('CmpDispl1 is currently not supported');

    case FEntryOffsets.GetCmpModifier(E) of
      // cmp dword ptr [R1], D2
      0: if D2 < $80 then Cmp.Opcode := [$83, $38 + R1, D2] else Cmp.Opcode := [$81, $38 + R1];
      // cmp byte ptr [R1], D2
      2: Cmp.Opcode := [$80, $38 + R1, D2];
      // cmp R1, D2
      4: if D2 < $80 then Cmp.Opcode := [$83, $F8 + R1, D2] else Cmp.Opcode := [$81, $F8 + R1];
      else raise Exception.CreateFmt('Unsupported cmp modifier: %d', [FEntryOffsets.GetCmpModifier(E)]);
    end;
    if Length(Cmp.Opcode) = 2 then // put imm32
    begin
      SetLength(Cmp.Opcode, 6);
      PCardinal(@Cmp.Opcode[2])^ := D2;
    end;
  end;

  Cmp.AbsTarget := High(UInt32);
  Cmp.Origin := FEntryOffsets.GetEntryOffset(E) + FAddress;

  FNewInstrs.Add(Cmp);

  RecoverJcc(E, True);
end;

procedure TRolyPoly.ProcessNewInstrs;
var
  Highest, K, Cursor: NativeUInt;
  Instr: TInstrDescr;
  ReqLen: UInt32;
begin
  Highest := 0;
  for K in FDisassembly.Keys do
    if K > Highest then
      Highest := K;

  // Assemble new instructions at the end of the code block.
  Cursor := Highest + FDisassembly[Highest].Reserved_[0] - FAddress;
  for Instr in FNewInstrs do
  begin
    ReqLen := Length(Instr.Opcode);
    if Instr.AbsTarget <> High(UInt32) then
      Inc(ReqLen, 4);

    if Cursor + ReqLen > FCodeSize then
    begin
      Inc(FCodeSize, $1000);
      ReallocMem(FCodeDump, FCodeSize);
    end;

    if Instr.Origin <> 0 then
    begin
      with FDisassembly[Instr.Origin]^ do
      begin
        Instruction.Opcode := $E9;
        PByte(EIP)^ := $E9;
        PInteger(EIP + 1)^ := Cursor - (Instr.Origin - FAddress) - 5;
      end;
    end;

    Move(Instr.Opcode[0], FCodeDump[Cursor], Length(Instr.Opcode));
    Inc(Cursor, Length(Instr.Opcode));

    if Instr.AbsTarget <> High(UInt32) then
    begin
      PInteger(FCodeDump + Cursor)^ := Instr.AbsTarget - Cursor - 4;
      Inc(Cursor, 4);
    end;
  end;
  // Set to actual size in use.
  FCodeSize := Cursor;
end;

procedure TRolyPoly.CleanupCodeDump;
var
  InUse: TList<Integer>;
  D: PDisasm;
  i: Integer;
  AllNop: Boolean;
begin
  // Nop trash bytes that are never executed.
  InUse := TList<Integer>.Create;
  try
    for D in FDisassembly.Values do
      for i := 0 to D^.Reserved_[0] - 1 do
        InUse.Add(D.VirtualAddr - FAddress + UInt32(i));

    for i := 0 to FCodeSize - 1 do
      if not InUse.Contains(i) then
        FCodeDump[i] := $90;
  finally
    InUse.Free;
  end;

  for D in FDisassembly.Values do
  begin
    // Delete odd jmp prefixes.
    if (D^.Instruction.Opcode = $EB) and (D^.Reserved_[0] = 3) then
      PByte(D^.EIP)^ := $90;

    // If it's a pretty short jump over nops, remove the jmp entirely.
    if (D^.Instruction.Opcode = $EB) and (D^.Instruction.AddrValue > D^.VirtualAddr) and (D^.Instruction.AddrValue - D^.VirtualAddr < 10) then
    begin
      AllNop := True;
      for i := D^.Reserved_[0] to D^.Instruction.AddrValue - D^.VirtualAddr - 1 do
        if PByte(D^.EIP + UInt32(i))^ <> $90 then
          AllNop := False;

      if AllNop then
        FillChar(PByte(D^.EIP)^, D^.Reserved_[0], $90);
    end;
  end;
end;

{ TEntryOffsets }

function TEntryOffsets.GetBranchType(E: Pointer): Byte;
begin
  Result := (PByte(E) + Offsets[phBranchType])^;
end;

function TEntryOffsets.GetCmpDispl1(E: Pointer): Integer;
begin
  Result := PInteger(PByte(E) + Offsets[phCmpDispl1])^;
end;

function TEntryOffsets.GetCmpDispl2(E: Pointer): Integer;
begin
  Result := PInteger(PByte(E) + Offsets[phCmpDispl2])^;
end;

function TEntryOffsets.GetCmpModifier(E: Pointer): Byte;
begin
  Result := (PByte(E) + Offsets[phCmpModifier])^;
end;

function TEntryOffsets.GetCmpReg1(E: Pointer): Byte;
begin
  Result := (PByte(E) + Offsets[phCmpReg1])^;
end;

function TEntryOffsets.GetCmpReg2(E: Pointer): Byte;
begin
  Result := (PByte(E) + Offsets[phCmpReg2])^;
end;

function TEntryOffsets.GetEntryOffset(E: Pointer): UInt32;
begin
  Result := PCardinal(PByte(E) + Offsets[phOffset])^ + Key;
end;

function TEntryOffsets.GetFlowType(E: Pointer): Byte;
begin
  Result := (PByte(E) + Offsets[phFlowType])^;
end;

function TEntryOffsets.GetTarget(E: Pointer): Integer;
begin
  Result := PCardinal(PByte(E) + Offsets[phTarget])^ + Key;
end;

function TEntryOffsets.GetTarget2(E: Pointer): Integer;
begin
  Result := PCardinal(PByte(E) + Offsets[phTarget2])^ + Key;
end;

{ TFixedPolyCode }

constructor TFixedPolyCode.Create(const AOriginalExtent: TMemoryRegion);
begin
  Fixups := TList<Integer>.Create;
  OriginalExtent := AOriginalExtent;
end;

destructor TFixedPolyCode.Destroy;
begin
  Fixups.Free;

  inherited;
end;

end.
