// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Outputs
    o,
    // Inputs
    clk,
    i,
    idx
);
  input clk;
  input [3:0] i;
  input idx;
  output [3:0] o;

  logic [1:0][3:0] array;

  always_comb array[0] = i;

  always @(posedge clk) array[0] <= array[0];

  struct {
    logic [3:0] a;
    logic [3:0] b;
  } unpacked;

  always_comb unpacked.a = i;

  always @(posedge clk) unpacked.b <= unpacked.a;

  // Also a blocking assignment in a function called from combinational logic, also through
  // another function
  logic [3:0] viaFunc;
  class Cls;
    static function void set(logic [3:0] v);
      viaFunc = v;
    endfunction
    static function void setViaOther(logic [3:0] v);
      set(v);
    endfunction
  endclass
  always @* Cls::setViaOther(i);

  always @(posedge clk) viaFunc <= viaFunc;

  // verilator lint_off MULTIDRIVEN
  // Unpacked array with an element possibly written by both
  logic [3:0] elems[2];

  always_comb elems[0] = i;

  always @(posedge clk) elems[idx] <= i;

  // Unpacked array with different elements written by each, which is fine
  logic [3:0] distinct[2];

  always_comb distinct[0] = i;

  always @(posedge clk) distinct[1] <= i;

  // Unpacked array too large to be split into its elements, written whole by one, so it
  // overlaps any element written by the other
  logic [3:0] whole[257];

  always_comb whole = '{default: i};

  always @(posedge clk) whole[1] <= i;

  // Interface instances, and a handle that might select either
  Ifc ifc1 ();
  Ifc ifc2 ();
  virtual Ifc vif = ifc1;

  // Combinational logic writing the instance the handle might select, and an NBA via the handle
  always @* ifc2.x = i;

  always @(posedge clk) vif.x <= i;

  // Combinational logic writing via the handle, and an NBA to an instance it might select
  always @* vif.y = i;

  always @(posedge clk) ifc1.y <= i;

  // No other process can write what a continuous assignment or always_comb writes, so the
  // handle selects another instance, which is fine
  assign ifc2.z = i;

  always @(posedge clk) vif.z <= i;

  always_comb ifc2.w = i;

  always @(posedge clk) vif.w <= i;
  // verilator lint_on MULTIDRIVEN

  assign o = array[idx] + unpacked.a + viaFunc + elems[idx] + distinct[idx] + whole[1];

endmodule

// verilator lint_off MULTIDRIVEN
interface Ifc;
  logic [3:0] x;
  logic [3:0] y;
  logic [3:0] z;
  logic [3:0] w;
endinterface
// verilator lint_on MULTIDRIVEN
