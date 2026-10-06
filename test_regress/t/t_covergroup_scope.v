// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Covergroups of one name in distinct scopes are distinct types, so the type coverage of each,
// get_coverage(), is of its own instances only (IEEE 1800-2023 19.3, 19.4, 19.11).  In each
// pair below one type is covered and the other is not; were they one type, both would be 50.
// A type is named as $typename names it (IEEE 1800-2023 20.6.1), with its scopes, generate blocks
// included, and the values of the parameters of its specializations; escaped identifiers are
// named escaped, as in hierarchical names (IEEE 1800-2023 23.6), so apart from the scopes their
// dots would name.

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg;
  class Holder;
    bit v;
    covergroup cg;
      cp: coverpoint v;
    endgroup
    function new;
      cg = new;
    endfunction
  endclass
endpackage

// Embedded covergroups of one name in two classes
class First;
  bit v;
  covergroup cg;
    cp: coverpoint v;
  endgroup
  function new;
    cg = new;
  endfunction
endclass

class Second;
  bit v;
  covergroup cg;
    cp: coverpoint v;
  endgroup
  function new;
    cg = new;
  endfunction
endclass

// A class of the name of a class in a package
class Holder;
  bit v;
  covergroup cg;
    cp: coverpoint v;
  endgroup
  function new;
    cg = new;
  endfunction
endclass

// The specializations of a class are distinct classes, but matching ones are one class, as the
// default specialization and Param #(1) (IEEE 1800-2023 8.25)
class Param #(
    int N = 1
);
  bit v;
  covergroup cg;
    cp: coverpoint v;
  endgroup
  function new;
    cg = new;
  endfunction
endclass

// An untyped parameter is of the type of its value (IEEE 1800-2023 6.20.2), so the specializations
// of values of distinct types are distinct, and named with sized values
class Untyped #(
    parameter P = 0
);
  bit v;
  covergroup cg;
    cp: coverpoint v;
  endgroup
  function new;
    cg = new;
  endfunction
endclass

// An embedded covergroup of an escaped name holding a dot, and one in nested class 'inner'
class Outer;
  class inner;
    bit v;
    covergroup cg;
      cp: coverpoint v;
    endgroup
    function new;
      cg = new;
    endfunction
  endclass
  bit v;
  covergroup \inner.cg ;
    cp: coverpoint v;
  endgroup
  function new;
    \inner.cg = new;
  endfunction
endclass

// A covergroup of an escaped name, outside any class
covergroup \cg+symbol with function sample (bit v);
  cp: coverpoint v;
endgroup

// Covergroups of one name in two modules
module sub_a;
  covergroup cg with function sample (bit v);
    cp: coverpoint v;
  endgroup
  cg inst = new;
endmodule

module sub_b;
  covergroup cg with function sample (bit v);
    cp: coverpoint v;
  endgroup
  cg inst = new;
endmodule

// The specializations of a module are distinct modules
module sub_p #(
    parameter int W = 1
);
  covergroup cg with function sample (bit v);
    cp: coverpoint v;
  endgroup
  cg inst = new;
endmodule

// Generate block 'gen_e' in module 'sub_e'
module sub_e;
  if (1) begin : gen_e
    covergroup cg with function sample (bit v);
      cp: coverpoint v;
    endgroup
    cg inst = new;
  end
endmodule

module t;
  covergroup cg with function sample (bit v);
    cp: coverpoint v;
  endgroup
  cg inst = new;

  // Each generate block is a scope, as is that of an 'else if'
  for (genvar i = 0; i < 2; ++i) begin : gen
    covergroup cg with function sample (bit v);
      cp: coverpoint v;
    endgroup
    cg inst = new;
  end
  if (0) begin : gen_if
  end
  else if (1) begin : gen_elif
    covergroup cg with function sample (bit v);
      cp: coverpoint v;
    endgroup
    cg inst = new;
  end
  // A covergroup of an escaped name holding a dot, and one in generate block 'gen_esc'
  if (1) begin : gen_esc
    covergroup cg with function sample (bit v);
      cp: coverpoint v;
    endgroup
    cg inst = new;
  end
  covergroup \gen_esc.cg with function sample (bit v);
    cp: coverpoint v;
  endgroup
  \gen_esc.cg esc_inst = new;
  // Escaped names of a generate block, of a class in it, and of the covergroup of the class
  if (1) begin : \pack+gen
    class \Klass! ;
      bit v;
      covergroup \cg@symbol2 ;
        cp: coverpoint v;
      endgroup
      function new;
        \cg@symbol2 = new;
      endfunction
    endclass
    \Klass! obj = new;
  end

  sub_a a ();
  sub_b b ();
  sub_p #(1) p1 ();
  sub_p #(2) p2 ();
  sub_e e2 ();

  First first;
  Second second;
  pkg::Holder pkg_holder;
  Holder holder;
  Param param0;
  Param #(1) param1;
  Param #(2) param2;
  Untyped #(1'b1) untyped1;
  Untyped #(8'd1) untyped8;
  Untyped #(1) untyped32;
  Untyped #(-8'sd5) untyped_neg;
  Outer outer;
  Outer::inner nested;
  \cg+symbol unit_sym = new;

  initial begin
    first = new;
    second = new;
    pkg_holder = new;
    holder = new;
    param0 = new;
    param1 = new;
    param2 = new;
    untyped1 = new;
    untyped8 = new;
    untyped32 = new;
    untyped_neg = new;
    outer = new;
    nested = new;

    // Cover the first type of each pair
    first.v = 0;
    first.cg.sample();
    first.v = 1;
    first.cg.sample();
    pkg_holder.v = 0;
    pkg_holder.cg.sample();
    pkg_holder.v = 1;
    pkg_holder.cg.sample();
    param1.v = 0;
    param1.cg.sample();
    param1.v = 1;
    param1.cg.sample();
    untyped1.v = 0;
    untyped1.cg.sample();
    untyped1.v = 1;
    untyped1.cg.sample();
    a.inst.sample(0);
    a.inst.sample(1);
    p1.inst.sample(0);
    p1.inst.sample(1);
    gen[0].inst.sample(0);
    gen[0].inst.sample(1);
    gen_elif.inst.sample(0);
    gen_elif.inst.sample(1);
    esc_inst.sample(0);
    esc_inst.sample(1);
    unit_sym.sample(0);
    unit_sym.sample(1);
    outer.v = 0;
    outer.\inner.cg .sample();
    outer.v = 1;
    outer.\inner.cg .sample();

    `checkr(first.cg.get_coverage(), 100.0);
    `checkr(second.cg.get_coverage(), 0.0);
    `checkr(pkg_holder.cg.get_coverage(), 100.0);
    `checkr(holder.cg.get_coverage(), 0.0);
    // get_coverage() is of the type, so of any of its instances
    `checkr(param0.cg.get_coverage(), param1.cg.get_coverage());
    `checkr(param2.cg.get_coverage(), 0.0);
    `checkr(untyped1.cg.get_coverage(), 100.0);
    `checkr(untyped8.cg.get_coverage(), 0.0);
    `checkr(untyped32.cg.get_coverage(), 0.0);
    `checkr(untyped_neg.cg.get_coverage(), 0.0);
    `checkr(a.inst.get_coverage(), 100.0);
    `checkr(b.inst.get_coverage(), 0.0);
    `checkr(p1.inst.get_coverage(), 100.0);
    `checkr(p2.inst.get_coverage(), 0.0);
    `checkr(e2.gen_e.inst.get_coverage(), 0.0);
    `checkr(gen[0].inst.get_coverage(), 100.0);
    `checkr(gen[1].inst.get_coverage(), 0.0);
    `checkr(gen_elif.inst.get_coverage(), 100.0);
    `checkr(esc_inst.get_coverage(), 100.0);
    `checkr(gen_esc.inst.get_coverage(), 0.0);
    `checkr(inst.get_coverage(), 0.0);
    `checkr(outer.\inner.cg .get_coverage(), 100.0);
    `checkr(nested.cg.get_coverage(), 0.0);
    `checkr(unit_sym.get_coverage(), 100.0);
    `checkr(\pack+gen .obj.\cg@symbol2 .get_coverage(), 0.0);
    // Named as $typename names them, so escaped
    `checks($typename(unit_sym), "class $unit::\\cg+symbol ");
    `checks($typename(\pack+gen .obj.\cg@symbol2 ), "class t.\\pack+gen .\\Klass! ::\\cg@symbol2 ");
    `checks($typename(esc_inst), "class t.\\gen_esc.cg ");
    `checks($typename(gen_esc.inst), "class t.gen_esc.cg");
    `checks($typename(untyped1), "class $unit::Untyped#(1'd1)");
    `checks($typename(untyped8), "class $unit::Untyped#(8'd1)");
    `checks($typename(untyped32), "class $unit::Untyped#(1)");
    `checks($typename(untyped_neg), "class $unit::Untyped#(-8'sd5)");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
