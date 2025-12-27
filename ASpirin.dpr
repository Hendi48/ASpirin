program ASpirin;

{$WEAKLINKRTTI ON}
{$RTTI EXPLICIT METHODS([]) PROPERTIES([]) FIELDS([])}

uses
  Vcl.Forms,
  Unit2 in 'Unit2.pas' {UnpackerWnd},
  DebuggerCore in 'DebuggerCore.pas',
  Utils in 'Utils.pas',
  Dumper in 'Dumper.pas',
  PEInfo in 'PEInfo.pas',
  BeaEngineDelphi32 in 'BeaEngineDelphi32.pas',
  ASProtect in 'ASProtect.pas',
  RestoreLibCode in 'RestoreLibCode.pas',
  Patcher in 'Patcher.pas',
  RolyPoly in 'RolyPoly.pas';

{$R *.res}

begin
  Application.Initialize;
  Application.MainFormOnTaskbar := True;
  Application.CreateForm(TUnpackerWnd, UnpackerWnd);
  Application.Run;
end.
