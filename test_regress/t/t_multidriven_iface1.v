// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// interface task chain - nested task calls write interface signal in same always_comb

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface my_if;
  logic l0;

  task set_l0_1_inner(); l0 = 1'b1; endtask
  task set_l0_1_outer(); set_l0_1_inner(); endtask
endinterface

module mod #()(
  input logic sel
  ,output logic val
);

  my_if if0();

  always_comb begin
    if0.l0 = 1'b0;

    if (sel) begin
      if0.set_l0_1_outer();
    end
  end

  assign val = if0.l0;

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
