// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

typedef enum bit [1:0] { TXN_READ, TXN_WRITE } txn_e;

// Each constraint exercises one RHS shape allowed by IEEE 1800-2023 18.7.2
// (constraint_set on the right of the implication operator -> ).  `mode`
// selects which constraint contributes; the others are vacuous.
class Forms;
  rand bit [3:0]  mode;
  rand bit [3:0]  a;
  rand bit [3:0]  b;
  rand bit [3:0]  c;
  rand bit [31:0] address;
  rand txn_e      txn_type;
  rand bit [7:0]  arr [4];
  rand bit [3:0]  uarr [3];

  // Bare expression (legacy form, supported pre-PR via expr->expr).
  constraint c_expr {
    (mode == 4'd0) -> b == 4'h9;
  }

  // Brace-block: the exact shape from issue #7300.
  constraint c_brace_repro {
    (mode == 4'd1) -> {
      if (txn_type inside {TXN_READ}) address % (1 << 4) == 0;
    }
  }

  // Brace-block with multiple statements.
  constraint c_brace_multi {
    (mode == 4'd2) -> {
      address[0]  == 1'b0;
      address[31] == 1'b0;
    }
  }

  // Bare if (without surrounding braces).
  constraint c_if {
    (mode == 4'd3) -> if (a == 4'h1) b == 4'h7;
  }

  // Bare if/else.
  constraint c_if_else {
    (mode == 4'd4) -> if (a == 4'h1) b == 4'ha;
                      else            b == 4'hb;
  }

  // Bare foreach.
  constraint c_foreach {
    (mode == 4'd5) -> foreach (arr[i]) arr[i] < 8'h40;
  }

  // Bare unique (uses the static-array form V3Randomize supports today).
  constraint c_unique {
    (mode == 4'd6) -> unique { uarr };
  }

  // Bare soft.
  constraint c_soft {
    (mode == 4'd7) -> soft b == 4'hd;
  }

  // Nested implication inside a brace block.
  constraint c_nested {
    (mode == 4'd8) -> {
      (a == 4'h0) -> { b == 4'h5; }
    }
  }
endclass

// Conditional `disable soft` is meta-level: V3Randomize hoists it into a
// runtime AstIf attached to the setup task so the directive only fires
// when its outer condition is true.  When override_flag==0, the soft
// `x == 4'h5` wins; when override_flag==1, the implication fires the
// disable AND the override `x == 4'hc`, so x must be 4'hc.
class DisSoft;
  bit override_flag;
  rand bit [3:0] x;
  constraint c_soft_x { soft x == 4'h5; }
  constraint c_override {
    (override_flag == 1'b1) -> disable soft x ;
    (override_flag == 1'b1) -> x == 4'hc ;
  }
endclass

module t;
  Forms   obj;
  DisSoft ds;
  int     ok;

  initial begin
    obj = new();

    repeat (10) begin
      ok = obj.randomize() with { mode == 4'd0; };
      `checkd(ok, 1);
      `checkh(obj.b, 4'h9);
    end

    repeat (10) begin
      ok = obj.randomize() with { mode == 4'd1; txn_type == TXN_READ; };
      `checkd(ok, 1);
      `checkh(obj.address[3:0], 4'h0);
    end

    repeat (10) begin
      ok = obj.randomize() with { mode == 4'd2; };
      `checkd(ok, 1);
      `checkh(obj.address[0], 1'b0);
      `checkh(obj.address[31], 1'b0);
    end

    repeat (10) begin
      ok = obj.randomize() with { mode == 4'd3; a == 4'h1; };
      `checkd(ok, 1);
      `checkh(obj.b, 4'h7);
    end

    repeat (10) begin
      ok = obj.randomize() with { mode == 4'd4; a == 4'h1; };
      `checkd(ok, 1);
      `checkh(obj.b, 4'ha);
    end
    repeat (10) begin
      ok = obj.randomize() with { mode == 4'd4; a == 4'h2; };
      `checkd(ok, 1);
      `checkh(obj.b, 4'hb);
    end

    repeat (10) begin
      ok = obj.randomize() with { mode == 4'd5; };
      `checkd(ok, 1);
      foreach (obj.arr[i]) `checkh(obj.arr[i] < 8'h40, 1'b1);
    end

    repeat (10) begin
      ok = obj.randomize() with { mode == 4'd6; };
      `checkd(ok, 1);
      `checkh(obj.uarr[0] == obj.uarr[1], 1'b0);
      `checkh(obj.uarr[0] == obj.uarr[2], 1'b0);
      `checkh(obj.uarr[1] == obj.uarr[2], 1'b0);
    end

    repeat (10) begin
      ok = obj.randomize() with { mode == 4'd7; };
      `checkd(ok, 1);
      `checkh(obj.b, 4'hd);
    end

    repeat (10) begin
      ok = obj.randomize() with { mode == 4'd8; a == 4'h0; };
      `checkd(ok, 1);
      `checkh(obj.b, 4'h5);
    end

    ds = new();
    ds.override_flag = 1'b0;
    repeat (10) begin
      ok = ds.randomize();
      `checkd(ok, 1);
      `checkh(ds.x, 4'h5);
    end
    ds.override_flag = 1'b1;
    repeat (10) begin
      ok = ds.randomize();
      `checkd(ok, 1);
      `checkh(ds.x, 4'hc);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
