// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A forced signal used as the index of an unpacked array select must read as
// forced, exactly as it does everywhere else (IEEE 1800-2023 10.6.2).
//
// Before the accompanying fix the array select kept reading the unforced
// value, while arithmetic on the same signal read the forced one.
//
// Both the continuous and the procedural read of the array are checked.  The
// controls are arithmetic on the same signal and a packed select on it, both
// of which were already correct.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module rf (
    input logic [3:0] raddr_i,
    output logic [7:0] rdata_o,
    output logic [7:0] plus_o,
    output logic [7:0] proc_o,
    output logic [7:0] packed_o
);
  logic [7:0] mem[16];
  logic [127:0] packed_mem;

  initial begin
    for (int i = 0; i < 16; ++i) mem[i] = 8'h10 + i[7:0];
    packed_mem = 128'h1f1e1d1c_1b1a1918_17161514_13121110;
  end

  // Array select on the forced index.
  assign rdata_o = mem[raddr_i];
  // Arithmetic on the same forced index, as the reference.
  assign plus_o = {4'h0, raddr_i} + 8'h1;
  // Packed select on the same forced index, as a second reference.
  assign packed_o = packed_mem[8*raddr_i+:8];

  // The same array select read procedurally rather than continuously.
  always_comb proc_o = mem[raddr_i];
endmodule

module t (
    input clk
);
  int cyc = 0;
  logic [3:0] addr;
  logic [7:0] rdata, plus, proc, packd;

  rf u_rf (
      .raddr_i(addr),
      .rdata_o(rdata),
      .plus_o(plus),
      .proc_o(proc),
      .packed_o(packd)
  );

  // Runtime-varying so the reads cannot be constant folded.
  assign addr = cyc[3:0];

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 4) force u_rf.raddr_i = 4'h7;
    if (cyc == 8) force u_rf.raddr_i = 4'ha;
    if (cyc == 12) release u_rf.raddr_i;
  end

  always @(negedge clk) begin
    case (cyc)
      2: begin  // Unforced: addr follows cyc.
        `checkh(rdata, 8'h12)
        `checkh(proc, 8'h12)
        `checkh(plus, 8'h03)
        `checkh(packd, 8'h12)
      end
      6: begin  // Forced to 7 while cyc says 6.
        `checkh(plus, 8'h08)
        `checkh(packd, 8'h17)
        `checkh(rdata, 8'h17)
        `checkh(proc, 8'h17)
      end
      10: begin  // Re-forced to 10 while cyc says 10, so only the value proves it.
        `checkh(plus, 8'h0b)
        `checkh(packd, 8'h1a)
        `checkh(rdata, 8'h1a)
        `checkh(proc, 8'h1a)
      end
      14: begin  // Released: back to following cyc.
        `checkh(plus, 8'h0f)
        `checkh(packd, 8'h1e)
        `checkh(rdata, 8'h1e)
        `checkh(proc, 8'h1e)
        $write("*-* All Finished *-*\n");
        $finish;
      end
      default: ;
    endcase
  end
endmodule
