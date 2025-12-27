unit Patcher;

interface

uses Windows, SysUtils, Classes, PEInfo, Generics.Collections, Math;

type
  TPatcher = class
  private
    FFileName: string;
    FStream: TMemoryStream;
    PE: TPEHeader;

    procedure SetSectionNamesAndCharacteristics;
    procedure FixupResources;
    procedure AdjustDataRawSize;
    procedure ShrinkPE;
  public
    constructor Create(const AFileName: string);
    destructor Destroy; override;

    procedure Process;
  end;

implementation

uses Unit2, Utils, DebuggerCore;

{ TPatcher }

constructor TPatcher.Create(const AFileName: string);
begin
  FFileName := AFileName;
  FStream := TMemoryStream.Create;
  FStream.LoadFromFile(AFileName);
  FStream.Position := 0;

  PE := TPEHeader.Create(FStream.Memory);
end;

destructor TPatcher.Destroy;
begin
  FStream.Free;
  PE.Free;

  inherited;
end;

procedure TPatcher.Process;
begin
  SetSectionNamesAndCharacteristics;
  AdjustDataRawSize;
  FixupResources; // depends on ShrinkPE to run after to lay out the section data correctly
  ShrinkPE;

  PE.SaveToStream(FStream); // saves the header
  FStream.SaveToFile(FFileName);
end;

procedure TPatcher.SetSectionNamesAndCharacteristics;
var
  Name: AnsiString;
begin
  Name := '.text'#0#0#0;
  Move(Name[1], PE.Sections[0].Header.Name[0], Length(Name));
  PE.Sections[0].Header.Characteristics := IMAGE_SCN_CNT_CODE or IMAGE_SCN_MEM_READ or IMAGE_SCN_MEM_EXECUTE;

  Name := '.rdata'#0#0#0;
  Move(Name[1], PE.Sections[1].Header.Name[0], Length(Name));
  PE.Sections[1].Header.Characteristics := IMAGE_SCN_CNT_INITIALIZED_DATA or IMAGE_SCN_MEM_READ;

  Name := '.data'#0#0#0;
  Move(Name[1], PE.Sections[2].Header.Name[0], Length(Name));
  PE.Sections[2].Header.Characteristics := IMAGE_SCN_CNT_INITIALIZED_DATA or IMAGE_SCN_MEM_READ or IMAGE_SCN_MEM_WRITE;

  // .rsrc
  PE.Sections[3].Header.Characteristics := IMAGE_SCN_CNT_INITIALIZED_DATA or IMAGE_SCN_MEM_READ;
end;

procedure TPatcher.FixupResources;
type
  TResource = record
    OffsetPtr: PCardinal;
    OffsetToData: Cardinal;
    Size: Integer;
  end;
var
  Rsrc: NativeUInt;
  AllRes: array of TResource;
  Extent: PByte;

  procedure ProcessDataEntry(EntPtr: PByte);
  begin
    SetLength(AllRes, Length(AllRes) + 1);
    with AllRes[High(AllRes)] do
    begin
      OffsetPtr := Pointer(EntPtr);
      OffsetToData := PCardinal(EntPtr)^;
      Size := PInteger(EntPtr + 4)^;
    end;

    if Extent < EntPtr + 16 then
      Extent := EntPtr + 16;
  end;

  procedure WalkDir(BasePtr, DirPtr: PByte);
  type
    TDirEnt = packed record
      Name, OffsetToData: Cardinal;
    end;
    PDirEnt = ^TDirEnt;
  var
    NumEnt: Int16;
    Ent: PDirEnt;
    i: Integer;
  begin
    NumEnt := PWord(DirPtr + $E)^;
    Ent := Pointer(DirPtr + $10);
    for i := 0 to NumEnt - 1 do
    begin
      if (Ent.OffsetToData and $80000000) <> 0 then
        WalkDir(BasePtr, BasePtr + (Ent.OffsetToData and $7FFFFFFF))
      else
        ProcessDataEntry(BasePtr + Ent.OffsetToData);

      Inc(Ent);
    end;
  end;

var
  NewData: TBytes;
  i, NewOffset: Integer;
begin
  // ASProtect moves some resources into its own section, so we reconstruct the rsrc section data.
  Rsrc := PE.NTHeaders.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_RESOURCE].VirtualAddress;

  Extent := nil;
  WalkDir(PByte(FStream.Memory) + Rsrc, PByte(FStream.Memory) + Rsrc); // Assuming file offset = virtual offset because it's a dump

  if Extent = nil then
  begin
    Log(ltInfo, 'No resources present');
    Exit;
  end;

  NewOffset := 0;
  for i := 0 to High(AllRes) do
  begin
    SetLength(NewData, Length(NewData) + AllRes[i].Size);
    Move((PByte(FStream.Memory) + AllRes[i].OffsetToData)^, NewData[NewOffset], AllRes[i].Size);
    AllRes[i].OffsetPtr^ := Cardinal(Extent - NativeUInt(FStream.Memory) + NewOffset);
    Inc(NewOffset, AllRes[i].Size);
  end;

  if Cardinal(Length(NewData)) + Cardinal(Extent - NativeUInt(FStream.Memory) - Rsrc) > PE.Sections[3].Header.SizeOfRawData then
    raise Exception.CreateFmt('Reconstructed .rsrc section exceeds size (%X > %X)', [Cardinal(Length(NewData)) + Cardinal(Extent - NativeUInt(FStream.Memory)), PE.Sections[3].Header.SizeOfRawData]);

  Move(NewData[0], Extent^, Length(NewData));
end;

procedure TPatcher.AdjustDataRawSize;
var
  i, RealSize: Integer;
  SData: TBytes;
begin
  RealSize := 0;

  with PE.Sections[2] do
  begin
    FStream.Seek(Header.PointerToRawData, soBeginning);
    SetLength(SData, Header.SizeOfRawData);
    FStream.Read(SData[0], Length(SData));
    for i := High(SData) downto 0 do
    begin
      if SData[i] <> 0 then
      begin
        RealSize := i;
        Break;
      end;
    end;

    if RealSize = 0 then
      Exit;

    if (RealSize and $FFF) <> 0 then
      RealSize := (RealSize + $1000) and not $FFF;

    Header.SizeOfRawData := RealSize;
    StreamDelta := Header.Misc.VirtualSize - Header.SizeOfRawData;
  end;

  for i := 3 to High(PE.Sections) do
    Dec(PE.Sections[i].Header.PointerToRawData, PE.Sections[2].StreamDelta);
end;

procedure TPatcher.ShrinkPE;
var
  i: Integer;
  Del: TList<Integer>;
  NS: TMemoryStream;

  function IsReferenced(SH: TImageSectionHeader): Boolean;
  var
    i: Integer;
  begin
    for i := 0 to High(PE.NTHeaders.OptionalHeader.DataDirectory) do
      with PE.NTHeaders.OptionalHeader.DataDirectory[i] do
      begin
        if (VirtualAddress >= SH.VirtualAddress) and (VirtualAddress + Size <= SH.VirtualAddress + SH.Misc.VirtualSize) then
          Exit(True);
      end;
    Result := False;
  end;

begin
  if (PE.NTHeaders.FileHeader.Characteristics and IMAGE_FILE_DLL) = 0 then
    FillChar(PE.NTHeaders.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC], SizeOf(TImageDataDirectory), 0);

  PE.Sections[4].Header.Name[0] := 0; // Make it not .data

  FStream.Position := 0;

  Del := TList<Integer>.Create;
  NS := TMemoryStream.Create;
  NS.CopyFrom(FStream, PE.Sections[0].Header.PointerToRawData);
  for i := 0 to High(PE.Sections) do
  begin
    if not IsReferenced(PE.Sections[i].Header) and (i > 0) and (PAnsiChar(@PE.Sections[i].Header.Name) <> '.data')
       and (PAnsiChar(@PE.Sections[i].Header.Name) <> '.poly') then
    begin
      Del.Add(i);
      if i <> High(PE.Sections) then
        FStream.Seek(PE.Sections[i + 1].Header.PointerToRawData - PE.Sections[i].Header.PointerToRawData, soCurrent);
    end
    else
    begin
      NS.CopyFrom(FStream, PE.Sections[i].Header.SizeOfRawData);
      FStream.Seek(PE.Sections[i].StreamDelta, soCurrent);
    end;
  end;
  FStream.Free;
  FStream := NS;

  Del.Reverse;
  for i in Del do
    PE.DeleteSection(i);
  Del.Free;
end;

end.
