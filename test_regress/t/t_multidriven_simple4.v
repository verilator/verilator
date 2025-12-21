// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module mod #()(
  input logic sel
  ,output logic val
);

  logic l0;

  task automatic set1(); l0 = 1'b1; endtask
  task automatic set0(); l0 = 1'b0; endtask

  always_comb begin
    set0();
    if (sel) begin
      set1();
    end
  end

  assign val = l0;

endmodule

module m_tb#()();

  logic sel, val;

  mod m(
    .sel(sel)
    ,.val(val)
  );

  initial begin
    #1;
    sel = 'b0;
    `checkd(val, 1'b0);
    #1;
    sel = 'b1;
    `checkd(val, 1'b1);
    #1;
    sel = 'b0;
    `checkd(val, 1'b0);
    #1;
  end

  initial begin
    #5;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
