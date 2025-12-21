// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// class function returns value - always_comb writes var directly + via class function call

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

class C;
  function automatic logic ret1();
    return 1'b1;
  endfunction
endclass

module mod #()(
  input logic sel
  ,output logic val
);

  logic l0;
  C c;

  initial c = new;

  always_comb begin
    l0 = 1'b0;
    if (sel) begin
      l0 = c.ret1();
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
