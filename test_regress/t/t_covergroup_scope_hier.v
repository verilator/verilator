// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// The specializations of a module are distinct modules, so the covergroups in them are distinct
// types (IEEE 1800-2023 19.3), wherever they are elaborated: the parent and hierarchical block
// 'hb' each specialize the modules below differently.  The parent's types are covered and hb's
// are not; were a type of the parent and one of hb one type, both would be 50.

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Of parameters whose values make a long name
module long_parameters #(
    parameter int FIRST_PARAMETER = 1,
    parameter int SECOND_PARAMETER = 2
);
  covergroup cg with function sample (bit v);
    cp: coverpoint v;
  endgroup
  cg inst = new;
endmodule

// Of a parameter not of 32 bits
module byte_parameter #(
    parameter bit [7:0] B = 8'd1
);
  covergroup cg with function sample (bit v);
    cp: coverpoint v;
  endgroup
  cg inst = new;
endmodule

// Of a type parameter
module type_parameter #(
    parameter type T = int
);
  covergroup cg with function sample (bit v);
    cp: coverpoint v;
  endgroup
  cg inst = new;
endmodule

module hb;
  /*verilator hier_block*/
  long_parameters #(1111111, 2222222) l ();
  byte_parameter #(8'd2) b ();
  type_parameter #(byte) p ();

  // After the parent's samples
  final begin
    `checkr(l.inst.get_coverage(), 0.0);
    `checkr(b.inst.get_coverage(), 0.0);
    `checkr(p.inst.get_coverage(), 0.0);
  end
endmodule

module t;
  long_parameters #(3333333, 4444444) l ();
  byte_parameter #(8'd3) b ();
  type_parameter #(shortint) p ();
  hb h ();

  initial begin
    l.inst.sample(0);
    l.inst.sample(1);
    b.inst.sample(0);
    b.inst.sample(1);
    p.inst.sample(0);
    p.inst.sample(1);
    $finish;
  end

  // Once hb's instances are constructed too
  final begin
    `checkr(l.inst.get_coverage(), 100.0);
    `checkr(b.inst.get_coverage(), 100.0);
    `checkr(p.inst.get_coverage(), 100.0);
    $write("*-* All Finished *-*\n");
  end
endmodule
