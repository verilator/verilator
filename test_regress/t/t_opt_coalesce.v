// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

interface Iface;
  // Must not coalesce: 'ival' is driven from outside by a different signal in each
  // instance, and the body below is dispatched on a virtual handle at run time, so
  // it has to read the signal of the instance it is called on, not one driver of it
  logic [31:0] ival;
  function automatic logic [31:0] get();
    return ival;
  endfunction
endinterface

class Cls;
  int val;
endclass

module t;

  logic clk = 0;
  always #5 clk = ~clk;

  integer cyc = 0;

  logic [31:0] src;
  always_comb src = {~cyc[15:0], cyc[15:0]};

  // Coalesced: a chain of copies, collapsed onto 'src' in a single pass, so
  // every read of them below is redirected at 'src'.
  logic [31:0] cp1;
  logic [31:0] cp2;
  logic [31:0] cp3;
  assign cp1 = src;
  assign cp2 = cp1;
  assign cp3 = cp2;

  // Coalesced: a combinational block holding nothing but a copy is the very
  // same thing as a continuous assignment
  logic [31:0] acb;
  always_comb acb = src;

  // Not coalesced: the block does more than copy one variable into another
  logic [31:0] acb2;
  logic [31:0] acb3;
  always_comb begin
    acb2 = src;
    acb3 = src;
  end

  // Not coalesced: a clocked block holds the value of the previous cycle
  logic [31:0] aff;
  always @(posedge clk) aff = src;

  // Not coalesced: a forced signal needs storage of its own
  logic [31:0] frc;
  assign frc = src;

  // Not coalesced: writable from the outside through the VPI
  logic [31:0] pub /*verilator public_flat_rw*/;
  assign pub = src;

  // Coalesced: a packed array of the same width holds the very same bits
  logic [3:0][7:0] arr;
  assign arr = src;

  // Not coalesced: a delayed assignment does not hold the value assigned
  logic [31:0] dly;
  assign #1 dly = src;

  // Not coalesced: a net delay makes the signal lag what drives it
  wire [31:0] #1 netdly;
  assign netdly = src;

  logic [31:0] srca = 32'h1111_1111;
  logic [31:0] srcb = 32'h2222_2222;
  Iface ifa ();
  Iface ifb ();
  assign ifa.ival = srca;
  assign ifb.ival = srcb;

  // Not coalesced: a handle refers to an object, it is not a plain value
  virtual Iface vifa;
  virtual Iface vifb;
  virtual Iface vifc;
  assign vifc = vifa;
  Cls obja = new;
  Cls objb;
  assign objb = obja;
  string stra = "str";
  string strb;
  assign strb = stra;

  initial begin
    vifa = ifa;
    vifb = ifb;
    obja.val = 42;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;

    // The copies hold exactly what they are assigned
    `checkh(cp1, src);
    `checkh(cp2, src);
    `checkh(cp3, src);
    `checkh(arr, src);
    `checkh(acb, src);
    `checkh(acb2, src);
    `checkh(acb3, src);
    `checkh(pub, src);
    `checkh(netdly, src);

    // A forced copy holds the forced value, the signal it copies is untouched
    if (cyc == 3) force frc = 32'hdead_beef;
    if (cyc == 4) begin
      `checkh(frc, 32'hdead_beef);
      `checkh(src, {~cyc[15:0], cyc[15:0]});
      `checkh(cp3, src);
      release frc;
    end
    if (cyc == 5) `checkh(frc, src);

    // The handles reach the object they were given, not some other one
    `checkh(vifa.get(), 32'h1111_1111);
    `checkh(vifb.get(), 32'h2222_2222);
    `checkh(vifc.get(), 32'h1111_1111);
    `checkh(objb.val, 42);
    `checks(strb, "str");

    if (cyc == 10) begin
      `checkh(dly, src);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
