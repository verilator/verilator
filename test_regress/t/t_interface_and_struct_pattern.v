// DESCRIPTION: Verilator: SystemVerilog interface test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

package Package_pkg;
    typedef struct packed {
        int bar;
        int baz;
    } pkg_struct_t;
endpackage

interface intf
  #(parameter type data_type = bit)
    (input wire clk,
     input wire rst);
    data_type data;
    modport source (
        input clk, rst,
        output data
    );
endinterface

module sub (
    intf.source bar,
    input clk,
    input rst);

    typedef struct packed {
        int foo;
        int baz;
    } struct_t;

    intf #(.data_type(struct_t)) the_intf (.*);

    Package_pkg::pkg_struct_t output_bar = Package_pkg::pkg_struct_t'{
        bar: the_intf.data.foo,
        baz: the_intf.data.baz
    };
endmodule

module t(clk);
    input clk;
     logic rst;

    intf bar (.*);
    sub the_sub (
        .bar(bar),
        .clk,
        .rst
    );

   // finish report
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
