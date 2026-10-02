// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Saqib Khan
// SPDX-License-Identifier: CC0-1.0

// Enum item referenced through a parameterized instance (#8347) (#8389)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface ifc #(
    parameter int W = 1
);
  typedef enum logic [3:0] {
    I_IDLE = 1,
    I_WORK = 4'(W)
  } state_t;
endinterface

module child #(
    parameter int W = 1
);
  typedef enum logic [4:0] {
    S_IDLE = 0,
    S_WORK = 5'(W)
  } state_t;
  state_t fsm = S_WORK;
  if (1) begin : blk
    typedef enum logic [4:0] {
      B_IDLE = 0,
      B_WORK = 5'(W + 10)
    } blk_t;
  end
  if (W == 1) begin : gif
    typedef enum logic [4:0] {G_ONE = 21} one_t;
  end else begin : gif
    typedef enum logic [4:0] {G_OTHER = 22} other_t;
  end
endmodule

module sub (
    ifc i
);
  int work;
  initial work = int'(i.I_WORK);
endmodule

module t;
  child #(.W(2)) a ();
  child #(.W(3)) b ();
  child c ();
  for (genvar g = 0; g < 2; ++g) begin : gen
    child #(.W(g + 4)) u ();
    wire working = u.fsm == u.S_WORK;
    int work = int'(u.S_WORK);
  end
  ifc #(.W(6)) i6 ();
  ifc #(.W(7)) i7[2] ();
  sub s (.i(i6));

  wire working = a.fsm == a.S_WORK;

  initial begin
    #1;
    `checkd(working, 1'b1);
    `checkd(a.S_IDLE, 0);
    `checkd(a.S_WORK, 2);
    `checkd(b.S_WORK, 3);
    `checkd(c.S_WORK, 1);
    `checkd(a.fsm, a.S_WORK);
    `checkd(b.fsm, b.S_WORK);
    `checkd(a.blk.B_WORK, 12);
    `checkd(t.b.blk.B_WORK, 13);
    `checkd(b.gif.G_OTHER, 22);
    `checkd(gen[0].working, 1'b1);
    `checkd(gen[1].working, 1'b1);
    `checkd(gen[0].work, 4);
    `checkd(gen[1].work, 5);
    `checkd(gen[0].u.S_WORK, 4);
    `checkd(gen[1].u.S_WORK, 5);
    `checkd(i6.I_WORK, 6);
    `checkd(i7[0].I_WORK, 7);
    `checkd(i7[1].I_WORK, 7);
    `checkd(s.work, 6);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
