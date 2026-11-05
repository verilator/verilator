// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define check(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

interface Ifc;
  logic [7:0] x = 8'd0;
endinterface

module t (
    input clk
);

  reg [31:0] cyc = 0;

  // 'x' has both blocking and non-blocking update, with the blocking
  // update in **clocked** logic
  reg [1:0] x = 2'b00;
  // '{y1, y0}' should have exactly the same value as 'x', at all times
  reg y0 = 1'b0;
  reg y1 = 1'b0;
  // 'z[0]' should equal '{8{x[0]}', 'z[1]' should equal '{8{x[1]}}'
  reg [1:0][7:0] z = '{default: 0};
  // 'pair.a' should equal 'x[0]', 'pair.b' should equal 'x[1]'
  struct {
    logic a;
    logic b;
  } pair = '{a: 1'b0, b: 1'b0};

  // 'ifc.x' has a non-blocking update, and a blocking update via a virtual
  // interface, also in clocked logic
  Ifc ifc ();
  virtual Ifc vif = ifc;

  always @(posedge clk) begin
    $display(
        "cyc = %d (%08x) x[1] = %0d, x[0] = %0d, y1 = %0d, y0 = %0d z[1] = %02x z[1] = %02x pair.a = %0d pair.b = %0d",
        cyc, cyc, x[1], x[0], y1, y0, z[1], z[0], pair.a, pair.b);
    `check(x[0], cyc[0]);
    `check(x[1], cyc[0]);
    `check(y0, cyc[0]);
    `check(y1, cyc[0]);
    `check(z[0], {8{cyc[0]}});
    `check(z[1], {8{cyc[0]}});
    `check(pair.a, cyc[0]);
    `check(pair.b, cyc[0]);
    x[1] <= ~x[1];
    y1 <= ~y1;
    for (int i = 0; i < 8; ++i) z[1][i] <= ~z[1][i];
    pair.b <= ~pair.b;
    begin
      // 'arr' has a non-blocking update of the whole array, and a blocking
      // update of an element, also in clocked logic. The blocking update
      // survives, unless the non-blocking update was also made.
      bit [7:0] arr[2];
      bit [7:0] ffs[2];
      ffs = '{8'hff, 8'hff};
      `check(arr[1], cyc[1:0] == 2'd1 ? 8'hff : cyc[7:0]);
      if (cyc[1:0] == 2'd0) arr <= ffs;
      arr[1] = cyc[7:0] + 8'd1;
    end
    begin
      // 'q' has a non-blocking update, and a blocking update by 'pop_front'
      // in the RHS of another non-blocking update, also in clocked logic.
      // The blocking update survives, unless the non-blocking update was
      // also made. 'q_exp' and 'val_exp' follow with blocking updates only.
      static int q[$] = '{0, 1, 2, 3};
      static int q_exp[$] = '{0, 1, 2, 3};
      static int val = 0;
      static int val_exp = 0;
      `check(q.size(), q_exp.size());
      `check(val, val_exp);
      val <= q.pop_front();
      val_exp = q_exp.pop_front();
      if (cyc[1:0] == 2'd3) begin
        q <= '{0, 1, 2, 3};
        q_exp = '{0, 1, 2, 3};
      end
    end
    // The blocking update via the virtual interface survives, unless the
    // non-blocking update was also made.
    `check(ifc.x, cyc[1:0] == 2'd1 ? 8'hff : cyc[7:0]);
    if (cyc[1:0] == 2'd0) ifc.x <= 8'hff;
    vif.x = cyc[7:0] + 8'd1;
    cyc = cyc + 1;
    x[0] = cyc[0];
    y0 = cyc[0];
    for (int i = 0; i < 8; ++i) z[0][i] = cyc[0];
    pair.a = cyc[0];
    if (cyc == 99) begin
      $display(x);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
