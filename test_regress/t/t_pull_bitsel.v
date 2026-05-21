// DESCRIPTION: Verilator: Test pullup/pulldown with bit-select assigns
//
// SPDX-FileCopyrightText: 2026 Lucas Amaral
// SPDX-License-Identifier: CC0-1.0

// Bug: When a module has bit-select assigns (e.g., out[17:0] = in[17:0])
// combined with pullup/pulldown tie cells for other bits, the enable
// for the assigns incorrectly covers all bits, causing the pull constant
// to be optimized away.

// verilator lint_off PINMISSING

// Tie cell with pullup/pulldown (like sky130_fd_sc_hd__conb)
module conb(output HI, output LO);
  pullup   pu (HI);
  pulldown pd (LO);
endmodule

// Wrapper that instantiates tie cell and connects to specific bit
module tiecell_1(output HI, output LO);
  conb base (.HI(HI), .LO(LO));
endmodule

// Parameterized tie cell for ranged connections; exercises the multi-bit
// SEL path in V3Tristate's per-bit pull tracking.
module tiecell_n #(parameter N = 1) (output [N-1:0] HI, output [N-1:0] LO);
  genvar gi;
  generate
    for (gi = 0; gi < N; gi = gi + 1) begin : g
      conb base (.HI(HI[gi]), .LO(LO[gi]));
    end
  endgenerate
endmodule

// Submodule mirroring the post-synthesis shape of a module whose outputs are
// constants implemented as tie cells: each output bit driven by exactly one
// tie cell of fixed direction. Per-bit pulls must propagate up to the parent
// net the submodule's output port is connected to.
module mask_col(output [7:0] out);
  conb t0 (.HI(out[0]));  // bit 0 = 1
  conb t1 (.LO(out[1]));  // bit 1 = 0
  conb t2 (.HI(out[2]));  // bit 2 = 1
  conb t3 (.LO(out[3]));  // bit 3 = 0
  conb t4 (.HI(out[4]));  // bit 4 = 1
  conb t5 (.LO(out[5]));  // bit 5 = 0
  conb t6 (.HI(out[6]));  // bit 6 = 1
  conb t7 (.LO(out[7]));  // bit 7 = 0
endmodule

module top(input [31:0] in_value, output [31:0] out_value);
  assign out_value[7:0] = in_value[7:0];

  // Bits 8-15: bit 15 pulled up, rest pulled down via single-bit and ranged cells.
  tiecell_1                       u_hi      (.HI(out_value[15]));
  tiecell_n #(.N(4))              u_lo_8_11 (.LO(out_value[11:8]));
  tiecell_1                       u_lo_8_dup(.LO(out_value[8]));
  tiecell_n #(.N(3))              u_lo_12_14(.LO(out_value[14:12]));

  // Bits 16-23 driven hierarchically through a part-select port connection.
  mask_col u_mask (.out(out_value[23:16]));

  assign out_value[31:24] = in_value[31:24];
endmodule

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;

  // Use wire with assign - values propagate in same delta cycle
  wire [31:0] in_value = 32'hDE00_0000;
  wire [31:0] out_value;

  top dut (.in_value(in_value), .out_value(out_value));

  // 0xDE = passthrough[31:24], 0x55 = mask_col HI/LO/HI/LO/HI/LO/HI/LO at [23:16],
  // 0x80 = bit 15 pullup + bits 14:8 pulldown, 0x00 = passthrough[7:0].
  wire [31:0] expected = 32'hDE55_8000;

  initial begin
    $display("in_value = %h, out_value = %h, expected = %h", in_value, out_value, expected);
    `checkh(out_value, expected);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
