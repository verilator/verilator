// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// static class task - call via class scope, writes through ref in same always_comb

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

class C;
  static task automatic set1(ref logic q);
    q = 1'b1;
  endtask
endclass

module mod #()(
  input logic sel
  ,output logic val
);

  logic l0;

  always_comb begin
    l0 = 1'b0;
    if (sel) begin
      C::set1(l0);
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
    #1;
    `checkd(val, 1'b0);
    sel = 'b1;
    #1;
    `checkd(val, 1'b1);
    sel = 'b0;
    #1;
    `checkd(val, 1'b0);
  end

  initial begin
    #5;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
