unit Unit2;

interface

uses
  Winapi.Windows, Winapi.Messages, System.SysUtils, System.Variants, System.Classes, Vcl.Graphics,
  Vcl.Controls, Vcl.Forms, Vcl.Dialogs, Vcl.StdCtrls, Vcl.ComCtrls, Vcl.ImgList, DebuggerCore,
  System.ImageList, Utils;

type
  TUnpackerWnd = class(TForm)
    btnUnpack: TButton;
    OD: TOpenDialog;
    LV: TListView;
    ImageList1: TImageList;
    procedure btnUnpackClick(Sender: TObject);
  private
    FDbg: TDebuggerCore;

    procedure Log(MsgType: TLogMsgType; const Msg: string);
  end;

var
  UnpackerWnd: TUnpackerWnd;

procedure Log(MsgType: TLogMsgType; const Msg: string);

implementation

uses ASProtect;

{$R *.dfm}

procedure Log(MsgType: TLogMsgType; const Msg: string);
begin
  UnpackerWnd.Log(MsgType, Msg);
end;

procedure TUnpackerWnd.btnUnpackClick(Sender: TObject);
begin
  if OD.Execute then
  begin
    FDbg := TASDebugger.Create(OD.FileName, '', Log);
  end;
end;

procedure TUnpackerWnd.Log(MsgType: TLogMsgType; const Msg: string);
begin
  with LV.Items.Add do
  begin
    Caption := Msg;
    ImageIndex := Integer(MsgType);
    MakeVisible(False);
  end;
end;

end.
