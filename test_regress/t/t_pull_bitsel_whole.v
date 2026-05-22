// DESCRIPTION: Verilator: Test per-bit pullup/pulldown propagation through whole-vector ports
//
// SPDX-FileCopyrightText: 2026 Lucas Amaral
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off PINMISSING

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module conb (
    output HI,
    output LO
);
  pullup pu (HI);
  pulldown pd (LO);
endmodule

module mask_col (
    output [7:0] out
);
  conb t0 (.HI(out[0]));
  conb t1 (.LO(out[1]));
  conb t2 (.HI(out[2]));
  conb t3 (.LO(out[3]));
  conb t4 (.HI(out[4]));
  conb t5 (.LO(out[5]));
  conb t6 (.HI(out[6]));
  conb t7 (.LO(out[7]));
endmodule

module pull_hi (
    output HI
);
  pullup pu (HI);
endmodule

module top (
    input [7:0] in_value,
    output [15:0] out_value,
    output [7:0] direct_mask,
    output direct_pull
);
  typedef struct packed {logic [1:0] field;} pair_t;

  wire [7:0] pulled;
  pair_t pair;

  assign out_value[7:0] = in_value;
  assign out_value[15:8] = pulled;
  assign pair.field[0] = in_value[0];

  // Whole-vector port connection. This exercises propagation of the child
  // module's per-bit pulls without the parent connection being a part-select.
  mask_col u_mask (.out(pulled));

  // Direct whole-vector/scalar output connections cover propagation to the
  // assignment target created for parent output ports.
  mask_col u_direct_mask (.out(direct_mask));
  pull_hi u_direct_pull (.HI(direct_pull));
endmodule

module t;
  wire [7:0] in_value = 8'hA6;
  wire [15:0] out_value;
  wire [7:0] direct_mask;
  wire direct_pull;

  top dut (
      .in_value(in_value),
      .out_value(out_value),
      .direct_mask(direct_mask),
      .direct_pull(direct_pull)
  );

  initial begin
    `checkh(out_value, 16'h55A6);
    `checkh(direct_mask, 8'h55);
    `checkh(direct_pull, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
