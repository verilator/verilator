// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

package some_pkg;
    localparam FOO = 5;
    localparam BAR = 6;

    typedef enum int {
        QUX = 7
    } pkg_enum_t;
endpackage

module t (/*AUTOARG*/
    // Inputs
    clk
    );

    input clk;
    int cyc = 0;

    logic [31:0] package_array [8];

    always_comb package_array = '{
        some_pkg::FOO: 32'h9876,
        some_pkg::BAR: 32'h1212,
        some_pkg::QUX: 32'h5432,
        default: 0
    };

    always_ff @(posedge clk) begin
        `checkh(package_array[5], 32'h9876);
        `checkh(package_array[6], 32'h1212);
        `checkh(package_array[7], 32'h5432);
    end

   always_ff @(posedge clk) begin
       cyc <= cyc + 1;
      if (cyc == 2) begin
          $write("*-* All Finished *-*\n");
          $finish;
      end
   end

endmodule
