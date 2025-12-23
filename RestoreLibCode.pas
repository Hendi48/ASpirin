unit RestoreLibCode;

// you steal? i restore!
// (this assumes your application is built with MSVC6)

interface

uses SysUtils;

type
  TReadFunc = function(Address: NativeUInt; Buf: Pointer; BufSize: NativeUInt): Boolean of object;

function GetStolenCode(Address, Stolen: NativeUInt; RPM: TReadFunc): TBytes;

implementation

uses Unit2, DebuggerCore, Utils, BeaEngineDelphi32;

const
  __EH_prolog: array[0..30] of Byte = (
    $6A, $FF, $50, $64, $A1, $00, $00, $00, $00, $50, $8B, $44, $24, $0C, $64, $89,
    $25, $00, $00, $00, $00, $89, $6C, $24, $0C, $8D, $6C, $24, $0C, $50, $C3
  );

  _memset: array[0..$57] of Byte = (
    $8B, $54, $24, $0C, $8B, $4C, $24, $04, $85, $D2, $74, $47, $33, $C0, $8A, $44,
    $24, $08, $57, $8B, $F9, $83, $FA, $04, $72, $2D, $F7, $D9, $83, $E1, $03, $74,
    $08, $2B, $D1, $88, $07, $47, $49, $75, $FA, $8B, $C8, $C1, $E0, $08, $03, $C1,
    $8B, $C8, $C1, $E0, $10, $03, $C1, $8B, $CA, $83, $E2, $03, $C1, $E9, $02, $74,
    $06, $F3, $AB, $85, $D2, $74, $06, $88, $07, $47, $4A, $75, $FA, $8B, $44, $24,
    $08, $5F, $C3, $8B, $44, $24, $04, $C3
  );

  _strlen: array[0..$7A] of Byte = (
    $8B, $4C, $24, $04, $F7, $C1, $03, $00, $00, $00, $74, $14, $8A, $01, $41, $84,
    $C0, $74, $40, $F7, $C1, $03, $00, $00, $00, $75, $F1, $05, $00, $00, $00, $00,
    $8B, $01, $BA, $FF, $FE, $FE, $7E, $03, $D0, $83, $F0, $FF, $33, $C2, $83, $C1,
    $04, $A9, $00, $01, $01, $81, $74, $E8, $8B, $41, $FC, $84, $C0, $74, $32, $84,
    $E4, $74, $24, $A9, $00, $00, $FF, $00, $74, $13, $A9, $00, $00, $00, $FF, $74,
    $02, $EB, $CD, $8D, $41, $FF, $8B, $4C, $24, $04, $2B, $C1, $C3, $8D, $41, $FE,
    $8B, $4C, $24, $04, $2B, $C1, $C3, $8D, $41, $FD, $8B, $4C, $24, $04, $2B, $C1,
    $C3, $8D, $41, $FC, $8B, $4C, $24, $04, $2B, $C1, $C3
  );

  __wincmdln_Template: array[0..$57] of Byte = ( // 4 dynamic dwords
    $83, $3D, $EE, $EE, $EE, $EE, $00, $75, $05, $E8, $EE, $EE, $EE, $EE, $56, $8B,
    $35, $EE, $EE, $EE, $EE, $8A, $06, $3C, $22, $75, $25, $8A, $46, $01, $46, $3C,
    $22, $74, $15, $84, $C0, $74, $11, $0F, $B6, $C0, $50, $E8, $EE, $EE, $EE, $EE,
    $85, $C0, $59, $74, $E6, $46, $EB, $E3, $80, $3E, $22, $75, $0D, $46, $EB, $0A,
    $3C, $20, $76, $06, $46, $80, $3E, $20, $77, $FA, $8A, $06, $84, $C0, $74, $04,
    $3C, $20, $76, $E9, $8B, $C6, $5E, $C3
  );

  __setenvp_Template: array[0..$B8] of Byte = ( // 16 dynamic dwords
    $53, $33, $DB, $39, $1D, $EE, $EE, $EE, $EE, $56, $57, $75, $05, $E8, $EE, $EE,
    $EE, $EE, $8B, $35, $EE, $EE, $EE, $EE, $33, $FF, $8A, $06, $3A, $C3, $74, $12,
    $3C, $3D, $74, $01, $47, $56, $E8, $EE, $EE, $EE, $EE, $59, $8D, $74, $06, $01,
    $EB, $E8, $8D, $04, $BD, $04, $00, $00, $00, $50, $E8, $EE, $EE, $EE, $EE, $8B,
    $F0, $59, $3B, $F3, $89, $35, $EE, $EE, $EE, $EE, $75, $08, $6A, $09, $E8, $EE,
    $EE, $EE, $EE, $59, $8B, $3D, $EE, $EE, $EE, $EE, $38, $1F, $74, $39, $55, $57,
    $E8, $EE, $EE, $EE, $EE, $8B, $E8, $59, $45, $80, $3F, $3D, $74, $22, $55, $E8,
    $EE, $EE, $EE, $EE, $3B, $C3, $59, $89, $06, $75, $08, $6A, $09, $E8, $EE, $EE,
    $EE, $EE, $59, $57, $FF, $36, $E8, $EE, $EE, $EE, $EE, $59, $83, $C6, $04, $59,
    $03, $FD, $38, $1F, $75, $C9, $5D, $FF, $35, $EE, $EE, $EE, $EE, $E8, $EE, $EE,
    $EE, $EE, $59, $89, $1D, $EE, $EE, $EE, $EE, $89, $1E, $5F, $5E, $C7, $05, $EE,
    $EE, $EE, $EE, $01, $00, $00, $00, $5B, $C3
  );

function MakeFuncRef(Ctx: PByte; CtxBase: NativeUInt; CallVA: NativeUInt; const Pattern: AnsiString): Cardinal;
var
  FuncAddr: Cardinal;
begin
  FuncAddr := FindDynamic(Pattern, Ctx, $15000);
  if FuncAddr = 0 then
    raise Exception.Create('Pattern ' + string(Pattern) + ' not found');

  Inc(FuncAddr, CtxBase);
  Result := FuncAddr - CallVA - 5;
end;

procedure FixupWincmdln(Address: NativeUInt; var Code: TBytes; Ctx: PByte; RPM: TReadFunc);
var
  CRT: PByte;
  CtxBase, CmdLine: NativeUInt;
begin
  GetMem(CRT, $15000);
  try
    CtxBase := Address - $10000;
    if not RPM(CtxBase, CRT, $15000) then
      RaiseLastOSError;

    PCardinal(@Code[2])^ := PCardinal(@Ctx[2])^;
    PCardinal(@Code[10])^ := MakeFuncRef(CRT, CtxBase, Address + 9, '833D????????0075126AFDE8'); // ___initmbctable
    PCardinal(@Code[$2C])^ := MakeFuncRef(CRT, CtxBase, Address + $2B, '6A046A00FF74240CE8????????83C40CC3'); // __ismbblead

    CmdLine := FindDynamic('A3????????E8????????A3????????E8????????E8', CRT, $15000);
    if CmdLine = 0 then
      raise Exception.Create('CmdLine not found');

    PCardinal(@Code[$11])^ := PCardinal(@CRT[CmdLine + 1])^;
  finally
    FreeMem(CRT);
  end;
end;

procedure FixupSetenvp(Address: NativeUInt; var Code: TBytes; Ctx: PByte; RPM: TReadFunc);
var
  CRT: PByte;
  CRTBase, EnvStrs, MiddleThing: NativeUInt;
begin
  GetMem(CRT, $15000);
  try
    CRTBase := Address - $10000;
    if not RPM(CRTBase, CRT, $15000) then
      RaiseLastOSError;

    PCardinal(@Code[5])^ := PCardinal(@Ctx[5])^;
    PCardinal(@Code[$AF])^ := PCardinal(@Ctx[5])^ - 4;
    PCardinal(@Code[$E])^ := MakeFuncRef(CRT, CRTBase, Address + $D, '833D????????0075126AFDE8'); // ___initmbctable
    EnvStrs := FindDynamic('A3????????E8????????E8????????E8????????8975D0', CRT, $15000);
    if EnvStrs = 0 then
      raise Exception.Create('EnvStrs not found');
    PCardinal(@Code[$14])^ := PCardinal(@CRT[EnvStrs + 1])^;
    MiddleThing := FindStatic('3BF38935', Ctx, $330) + 4;
    if MiddleThing = 4 then
      MiddleThing := FindDynamic('8935????????E8????????6A09', Ctx, $330) + 2;
    if MiddleThing = 2 then
      raise Exception.Create('Address scan in polymorphic code failed');
    PCardinal(@Code[$46])^ := PCardinal(@Ctx[MiddleThing])^;
    PCardinal(@Code[$56])^ := PCardinal(@CRT[EnvStrs + 1])^;
    PCardinal(@Code[$99])^ := PCardinal(@CRT[EnvStrs + 1])^;
    PCardinal(@Code[$A5])^ := PCardinal(@CRT[EnvStrs + 1])^;
    PCardinal(@Code[$27])^ := MakeFuncRef(CRT, CRTBase, Address + $26, '8B4C2404F7C10300000074148A0141'); // _strlen
    PCardinal(@Code[$3B])^ := MakeFuncRef(CRT, CRTBase, Address + $3A, 'FF35????????FF742408E8????????5959C3'); // _malloc
    PCardinal(@Code[$4F])^ := MakeFuncRef(CRT, CRTBase, Address + $4E, '833D????????017505E8????????FF742404E8????????68FF000000FF15'); // __amsg_exit
    PCardinal(@Code[$61])^ := MakeFuncRef(CRT, CRTBase, Address + $60, '8B4C2404F7C10300000074148A0141'); // _strlen
    PCardinal(@Code[$70])^ := MakeFuncRef(CRT, CRTBase, Address + $6F, 'FF35????????FF742408E8????????5959C3'); // _malloc
    PCardinal(@Code[$7E])^ := MakeFuncRef(CRT, CRTBase, Address + $7D, '833D????????017505E8????????FF742404E8????????68FF000000FF15'); // __amsg_exit
    PCardinal(@Code[$87])^ := MakeFuncRef(CRT, CRTBase, Address + $86, '578B7C2408EB6A'); // _strcpy
    try
      PCardinal(@Code[$9E])^ := MakeFuncRef(CRT, CRTBase, Address + $9D, '5356578B750885F6') - $20; // some free func, pattern starts 0x20 in
    except
      PCardinal(@Code[$9E])^ := MakeFuncRef(CRT, CRTBase, Address + $9D, '568B74240885F6743D6A09E8'); // _free
    end;
  finally
    FreeMem(CRT);
  end;
end;

function GetStolenCode(Address, Stolen: NativeUInt; RPM: TReadFunc): TBytes;
var
  Dis: TDisasm;
  CodeBuf: array[0..$330-1] of Byte;
  L, i: Integer;
  S: string;
begin
  if not RPM(Stolen, @CodeBuf, SizeOf(CodeBuf)) then
  begin
    Log(ltFatal, Format('Reading %X bytes at %X failed', [SizeOf(CodeBuf), Stolen]));
    RaiseLastOSError;
  end;

  if (CodeBuf[0] = $68) and (PCardinal(@CodeBuf[1])^ = $FFFFFFFF) and ((CodeBuf[5] = $50) or (CodeBuf[5] = $EB) or ((CodeBuf[5] = $F3) and (CodeBuf[6] = $EB))) then
  begin
    Log(ltGood, 'Identified __EH_prolog');
    SetLength(Result, Length(__EH_prolog));
    Move(__EH_prolog, Result[0], Length(Result));
    Exit;
  end
  else if (PCardinal(@CodeBuf[0])^ = $0C24548B) and (PCardinal(@CodeBuf[4])^ = $04244C8B) then
  begin
    Log(ltGood, 'Identified _memset');
    SetLength(Result, Length(_memset));
    Move(_memset, Result[0], Length(Result));
    Exit;
  end
  else if (PCardinal(@CodeBuf[0])^ = $04244C8B) and (PCardinal(@CodeBuf[4])^ = $0003C1F7) then
  begin
    Log(ltGood, 'Identified _strlen');
    SetLength(Result, Length(_strlen));
    Move(_strlen, Result[0], Length(Result));
    Exit;
  end
  else if (CodeBuf[0] = $83) and (CodeBuf[1] = $3D) and (CodeBuf[6] = 0) then
  begin
    Log(ltGood, 'Identified __wincmdln');
    SetLength(Result, Length(__wincmdln_Template));
    Move(__wincmdln_Template, Result[0], Length(Result));
    FixupWincmdln(Address, Result, @CodeBuf, RPM);
    Exit;
  end
  else if (PCardinal(@CodeBuf[0])^ = $39DB3353) and (CodeBuf[8] = 0) then
  begin
    Log(ltGood, 'Identified __setenvp');
    SetLength(Result, Length(__setenvp_Template));
    Move(__setenvp_Template, Result[0], Length(Result));
    FixupSetenvp(Address, Result, @CodeBuf, RPM);
    Exit;
  end;

  S := '';
  FillChar(Dis, SizeOf(Dis), 0);
  Dis.EIP := NativeUInt(@CodeBuf);
  Dis.VirtualAddr := Stolen;
  for i := 0 to 2 do
  begin
    L := Disasm(Dis);
    if L <= 0 then
      Break;

    Inc(Dis.EIP, L);
    Inc(Dis.VirtualAddr, L);

    if S <> '' then
      S := S + '; ';
    S := S + string(AnsiString(Dis.CompleteInstr));
  end;

  Log(ltFatal, S);
  Log(ltFatal, Format('%.2X %.2X %.2X %.2X %.2X %.2X %.2X %.2X', [CodeBuf[0], CodeBuf[1], CodeBuf[2], CodeBuf[3], CodeBuf[4], CodeBuf[5], CodeBuf[6], CodeBuf[7]]));
  Result := nil;
end;

end.
