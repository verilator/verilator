// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class item_cls #(
    type T = int
);
  rand T value;
endclass

class multi_param_cls #(
    type T = int,
    int WIDTH = 8
);
  rand T data;
  rand bit [WIDTH-1:0] mask;
endclass

class driver_cls #(
    type T = int
);
  function int do_rand(T val);
    item_cls #(T) itemp;
    itemp = new();
    void'(itemp.randomize() with {value == local:: val;});
    return (itemp.value == val) ? 32'd1 : 32'd0;
  endfunction
endclass

class multi_driver_cls #(
    type T = int,
    int WIDTH = 8
);
  function int do_rand(T val, bit [WIDTH-1:0] m);
    multi_param_cls #(T, WIDTH) itemp;
    itemp = new();
    void'(itemp.randomize() with {
      data == local:: val;
      mask == local:: m;
    });
    return (itemp.data == val && itemp.mask == m) ? 32'd1 : 32'd0;
  endfunction
endclass

module t;
  initial begin
    driver_cls #(int) drvp;
    multi_driver_cls #(int, 8) mdrvp;

    drvp = new();
    mdrvp = new();

    repeat (20) begin
      `checkd(drvp.do_rand(32'd42), 32'd1)
    end

    repeat (20) begin
      `checkd(mdrvp.do_rand(32'd99, 8'hAB), 32'd1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
