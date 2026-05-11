// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class FassignBody;
  rand int b1;
  rand int b2;
  function int F(input int d);
    F = d;
  endfunction
  constraint c1 {b1 inside {[4'd1 : 4'd9]};}
  constraint c2 {b2 == F(b1);}
endclass

class Freturn;
  rand int b1;
  rand int b2;
  function int F(input int d);
    return d;
  endfunction
  constraint c1 {b1 inside {[4'd1 : 4'd9]};}
  constraint c2 {b2 == F(b1);}
endclass

class Fmultiarg;
  rand int b1;
  rand int b2;
  rand int b3;
  function int F(input int x, input int y);
    F = y;
  endfunction
  constraint c1 {b1 inside {[4'd1 : 4'd9]};}
  constraint c2 {b2 inside {[8'd20 : 8'd40]};}
  constraint c3 {b3 == F(b1, b2);}
endclass

class Fnonrand;
  rand int b2;
  int k;
  function int F(input int d);
    F = d;
  endfunction
  constraint c {b2 == F(k);}
endclass

module t;
  FassignBody o1;
  Freturn o2;
  Fmultiarg o3;
  Fnonrand o4;
  int rand_ok;

  initial begin
    o1 = new;
    o2 = new;
    o3 = new;
    o4 = new;

    repeat (20) begin
      rand_ok = o1.randomize();
      `checkd(rand_ok, 1)
      `checkd(o1.b2, o1.b1)

      rand_ok = o2.randomize();
      `checkd(rand_ok, 1)
      `checkd(o2.b2, o2.b1)

      rand_ok = o3.randomize();
      `checkd(rand_ok, 1)
      `checkd(o3.b3, o3.b2)

      o4.k = $urandom_range(32'd100, 32'd1);
      rand_ok = o4.randomize();
      `checkd(rand_ok, 1)
      `checkd(o4.b2, o4.k)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
