// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// Consolidated class-based task/function multidriven tests
// (formerly t_multidriven_class{0,1,2,3,4,f0,f1}.v)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

//----------------------------------------------------------------------
// class0: class task writes through ref argument (direct assignment + class task in same always_comb)

class C0;
  task automatic set1(ref logic q);
    q = 1'b1;
  endtask
  task automatic set0(ref logic q);
    q = 1'b0;
  endtask
endclass

module class0 #(
) (
    input logic sel,
    output logic val
);

  logic l0;
  C0 c;

  initial c = new;

  always_comb begin
    l0 = 1'b0;
    if (sel) begin
      c.set1(l0);
    end
  end

  assign val = l0;

endmodule

//----------------------------------------------------------------------
// class1: class task chain - nested method calls write through ref in same always_comb

class C1;
  task automatic inner(inout logic q);
    q = 1'b1;
  endtask
  task automatic outer(inout logic q);
    inner(q);
  endtask
endclass

module class1 #(
) (
    input logic sel,
    output logic val
);

  logic l0;
  C1 c;

  initial c = new;

  always_comb begin
    l0 = 1'b0;
    if (sel) begin
      c.outer(l0);
    end
  end

  assign val = l0;

endmodule

//----------------------------------------------------------------------
// class2: class handle passed through module port - class method writes through ref

class C2;
  task automatic set1(ref logic q);
    q = 1'b1;
  endtask
endclass

module class2 #(
) (
    input logic sel,
    output logic val,
    C2 c
);

  logic l0;

  always_comb begin
    l0 = 1'b0;
    if (sel) begin
      c.set1(l0);
    end
  end

  assign val = l0;

endmodule

//----------------------------------------------------------------------
// class3: static class task - call via class scope, writes through ref in same always_comb

class C3;
  static task automatic set1(ref logic q);
    q = 1'b1;
  endtask
endclass

module class3 #(
) (
    input logic sel,
    output logic val
);

  logic l0;

  always_comb begin
    l0 = 1'b0;
    if (sel) begin
      C3::set1(l0);
    end
  end

  assign val = l0;

endmodule

//----------------------------------------------------------------------
// class4: class composition - one class calls another task, ultimately writes through ref

class C4Inner;
  task automatic set1(ref logic q);
    q = 1'b1;
  endtask
endclass

class C4Outer;
  C4Inner inner;
  function new();
    inner = new;
  endfunction
  task automatic set1(ref logic q);
    inner.set1(q);
  endtask
endclass

module class4 #(
) (
    input logic sel,
    output logic val
);

  logic l0;
  C4Outer c;

  initial c = new;

  always_comb begin
    l0 = 1'b0;
    if (sel) begin
      c.set1(l0);
    end
  end

  assign val = l0;

endmodule

//----------------------------------------------------------------------
// classf0: class function returns value - always_comb writes var directly + via class function call

class Cf0;
  function automatic logic ret1();
    return 1'b1;
  endfunction
endclass

module classf0 #(
) (
    input logic sel,
    output logic val
);

  logic l0;
  Cf0 c;

  initial c = new;

  always_comb begin
    l0 = 1'b0;
    if (sel) begin
      l0 = c.ret1();
    end
  end

  assign val = l0;

endmodule

//----------------------------------------------------------------------
// classf1: static class function returns value - always_comb uses class scope call

class Cf1;
  static function automatic logic ret1();
    return 1'b1;
  endfunction
endclass

module classf1 #(
) (
    input logic sel,
    output logic val
);

  logic l0;

  always_comb begin
    l0 = 1'b0;
    if (sel) begin
      l0 = Cf1::ret1();
    end
  end

  assign val = l0;

endmodule

//----------------------------------------------------------------------
// Shared TB

module m_tb #() ();

  logic sel;

  logic val0, val1, val2, val3, val4, valf0, valf1;

  C2 c2;
  initial c2 = new;

  class0 u0 (
      .sel(sel),
      .val(val0)
  );
  class1 u1 (
      .sel(sel),
      .val(val1)
  );
  class2 u2 (
      .sel(sel),
      .val(val2),
      .c(c2)
  );
  class3 u3 (
      .sel(sel),
      .val(val3)
  );
  class4 u4 (
      .sel(sel),
      .val(val4)
  );
  classf0 uf0 (
      .sel(sel),
      .val(valf0)
  );
  classf1 uf1 (
      .sel(sel),
      .val(valf1)
  );

  task automatic check_all(input logic exp);
    `checkd(val0, exp);
    `checkd(val1, exp);
    `checkd(val2, exp);
    `checkd(val3, exp);
    `checkd(val4, exp);
    `checkd(valf0, exp);
    `checkd(valf1, exp);
  endtask

  initial begin
    #1;
    sel = 'b0;
    #1;
    check_all(1'b0);

    sel = 'b1;
    #1;
    check_all(1'b1);

    sel = 'b0;
    #1;
    check_all(1'b0);
  end

  initial begin
    #5;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
