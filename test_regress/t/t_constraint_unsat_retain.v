// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 18.6.3: "If randomize() fails, the constraints are infeasible, and the
// random variables retain their previous values."

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Inner;
  rand bit [14:0] p;
  rand bit [14:0] q;
endclass

class Plain;
  rand bit [6:0] c;
  rand bit [14:0] u;  // In no constraint
  constraint bad {
    c > 100;
    c < 50;
  }
endclass

class Satisfiable;
  rand bit [6:0] c;
  rand bit [14:0] u;  // In no constraint
  constraint good {c < 50;}
endclass

class Nested;
  rand bit [6:0] c;
  rand Inner inner;
  constraint bad {
    c > 100;
    c < 50;
  }
  function new();
    inner = new;
  endfunction
endclass

class Global;
  rand bit [6:0] c;
  rand Inner inner;
  constraint g {
    inner.p == 15'(c);
    c > 100;
    c < 50;
  }
  function new();
    inner = new;
  endfunction
endclass

class Base;
  rand bit [6:0] b;
endclass

class WithNested extends Base;
  rand bit [14:0] u;
  rand Inner inner;
  function new();
    inner = new;
  endfunction
endclass

// Also randomized on its own, so Owner's randomize() calls Solo's randomize()
class Solo;
  rand bit [14:0] s;
  constraint s_range {s > 10;}
endclass

class Owner;
  rand bit [6:0] c;
  rand Solo solo;
  constraint bad {
    c > 100;
    c < 50;
  }
  function new();
    solo = new;
  endfunction
endclass

class NoRand;
  bit [6:0] x;
endclass

class NullHandle;
  rand bit [6:0] c;
  rand Inner inner;  // Left null
  rand NoRand norand;
  function new();
    norand = new;
  endfunction
endclass

typedef class CycB;

class CycA;
  rand bit [6:0] c;
  rand CycB b;
endclass

class CycB;
  rand bit [14:0] z;
  rand CycA a;  // Left null
endclass

class ArrayOwner;
  rand bit [6:0] c;
  rand Inner items[2];
  function new();
    foreach (items[i]) items[i] = new;
  endfunction
endclass

module t;
  initial begin
    // randomize(): the solver fails, so the member it does not own is not filled
    begin
      Plain pl;
      int randomize_result;
      pl = new;
      pl.c = 11;
      pl.u = 12;
      randomize_result = pl.randomize();
      `checkd(randomize_result, 0);
      `checkd(pl.c, 11);
      `checkd(pl.u, 12);
    end

    // randomize() with: the member the solver does not own keeps its value; a call
    // that succeeds keeps the solver's values
    begin
      Satisfiable sa;
      int randomize_result;
      sa = new;
      sa.c = 11;
      sa.u = 12;
      randomize_result = sa.randomize() with {c > 60;};
      `checkd(randomize_result, 0);
      `checkd(sa.c, 11);
      `checkd(sa.u, 12);
      randomize_result = sa.randomize() with {c > 40;};
      `checkd(randomize_result, 1);
      if (sa.c <= 40 || sa.c >= 50) `stop;
    end

    // A rand class member keeps its values
    begin
      Nested ne;
      int randomize_result;
      ne = new;
      ne.c = 13;
      ne.inner.p = 14;
      ne.inner.q = 15;
      randomize_result = ne.randomize();
      `checkd(randomize_result, 0);
      `checkd(ne.c, 13);
      `checkd(ne.inner.p, 14);
      `checkd(ne.inner.q, 15);
    end

    // A global constraint: the constrained and unconstrained members of the sub-object
    begin
      Global gl;
      int randomize_result;
      gl = new;
      gl.c = 15;
      gl.inner.p = 16;
      gl.inner.q = 17;
      randomize_result = gl.randomize();
      `checkd(randomize_result, 0);
      `checkd(gl.c, 15);
      `checkd(gl.inner.p, 16);
      `checkd(gl.inner.q, 17);
    end

    // randomize() with on members without class constraints: an inherited member, an own
    // member, and the members of a rand class member
    begin
      WithNested wn;
      int randomize_result;
      wn = new;
      wn.b = 1;
      wn.u = 2;
      wn.inner.p = 3;
      wn.inner.q = 4;
      randomize_result = wn.randomize() with {
        u > 10;
        u < 5;
      };
      `checkd(randomize_result, 0);
      randomize_result = wn.randomize() with {
        inner.p > 10;
        inner.p < 5;
      };
      `checkd(randomize_result, 0);
      `checkd(wn.b, 1);
      `checkd(wn.u, 2);
      `checkd(wn.inner.p, 3);
      `checkd(wn.inner.q, 4);
      randomize_result = wn.randomize() with {inner.p == 7;};
      `checkd(randomize_result, 1);
      `checkd(wn.inner.p, 7);
    end

    // A rand class member that is randomized on its own, by its randomize()
    begin
      Solo so;
      Owner ow;
      int randomize_result;
      so = new;
      randomize_result = so.randomize();
      `checkd(randomize_result, 1);
      ow = new;
      ow.c = 21;
      ow.solo.s = 22;
      randomize_result = ow.randomize();
      `checkd(randomize_result, 0);
      randomize_result = ow.randomize() with {c < 40;};
      `checkd(randomize_result, 0);
      `checkd(ow.c, 21);
      `checkd(ow.solo.s, 22);
    end

    // A null rand class member, and one without rand members
    begin
      NullHandle nh;
      int randomize_result;
      nh = new;
      nh.c = 31;
      nh.norand.x = 32;
      randomize_result = nh.randomize() with {
        c > 100;
        c < 50;
      };
      `checkd(randomize_result, 0);
      `checkd(nh.c, 31);
      `checkd(nh.norand.x, 32);
    end

    // A class without rand members
    begin
      NoRand nr;
      int randomize_result;
      nr = new;
      nr.x = 3;
      randomize_result = nr.randomize() with {x == 5;};
      `checkd(randomize_result, 0);
      `checkd(nr.x, 3);
    end

    // Rand class members whose classes refer to each other
    begin
      CycA ca;
      int randomize_result;
      ca = new;
      ca.b = new;
      ca.c = 41;
      ca.b.z = 42;
      randomize_result = ca.randomize() with {
        c > 100;
        c < 50;
      };
      `checkd(randomize_result, 0);
      `checkd(ca.c, 41);
      `checkd(ca.b.z, 42);
    end

    // A rand array of class handles keeps its handles
    begin
      ArrayOwner ao;
      Inner first;
      int randomize_result;
      ao = new;
      ao.c = 51;
      first = ao.items[0];
      randomize_result = ao.randomize() with {
        c > 100;
        c < 50;
      };
      `checkd(randomize_result, 0);
      `checkd(ao.c, 51);
      if (ao.items[0] != first) `stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
