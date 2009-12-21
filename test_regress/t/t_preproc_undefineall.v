// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t;

`define UDALL
`ifndef PREDEF_COMMAND_LINE `error "Test setup error, PREDEF_COMMAND_LINE pre-missing" `endif

`undefineall

`ifdef UDALL `error "undefineall failed" `endif
`ifndef PREDEF_COMMAND_LINE `error "Deleted too much, no PREDEF_COMMAND_LINE" `endif

  initial begin
     $finish;
  end
endmodule
