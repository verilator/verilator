
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// direct task call
module mod0 #(
) (
    input logic sel,
    output logic val
);
  logic l0;
  task do_stuff();
    l0 = 'b1;
  endtask
  always_comb begin
    l0 = 'b0;
    if (sel) begin
      do_stuff();
    end
  end
  assign val = l0;
endmodule

// nested task call chain
module mod1 #(
) (
    input logic sel,
    output logic val
);
  logic l0;
  task do_inner();
    l0 = 'b1;
  endtask
  task do_outer();
    do_inner();
  endtask
  always_comb begin
    l0 = 'b0;
    if (sel) do_outer();
  end
  assign val = l0;
endmodule

// task writes through an output arguement
module mod2 #(
) (
    input logic sel,
    output logic val
);
  logic l0;
  task automatic do_stuff(output logic q);
    q = 1'b1;
  endtask
  always_comb begin
    l0 = 1'b0;
    if (sel) do_stuff(l0);
  end
  assign val = l0;
endmodule

// function call that writes
module mod3 #(
) (
    input logic sel,
    output logic val
);
  logic l0;
  function automatic void do_func();
    l0 = 1'b1;
  endfunction
  always_comb begin
    l0 = 1'b0;
    if (sel) do_func();
  end
  assign val = l0;
endmodule

// two tasks set0/set1
module mod4 #(
) (
    input logic sel,
    output logic val
);
  logic l0;
  task automatic set1();
    l0 = 1'b1;
  endtask
  task automatic set0();
    l0 = 1'b0;
  endtask
  always_comb begin
    set0();
    if (sel) begin
      set1();
    end
  end
  assign val = l0;
endmodule

module m_tb;
  logic sel;
  logic v0, v1, v2, v3, v4;

  mod0 u0 (
      .sel(sel),
      .val(v0)
  );
  mod1 u1 (
      .sel(sel),
      .val(v1)
  );
  mod2 u2 (
      .sel(sel),
      .val(v2)
  );
  mod3 u3 (
      .sel(sel),
      .val(v3)
  );
  mod4 u4 (
      .sel(sel),
      .val(v4)
  );

  initial begin
    #1;
    sel = 0;
    `checkd(v0, 0);
    `checkd(v1, 0);
    `checkd(v2, 0);
    `checkd(v3, 0);
    `checkd(v4, 0);
    #1;
    sel = 1;
    `checkd(v0, 1);
    `checkd(v1, 1);
    `checkd(v2, 1);
    `checkd(v3, 1);
    `checkd(v4, 1);
    #1;
    sel = 0;
    `checkd(v0, 0);
    `checkd(v1, 0);
    `checkd(v2, 0);
    `checkd(v3, 0);
    `checkd(v4, 0);
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
