// DESCRIPTION: Verilator: Verilog Test module
//
// This test examines Verilator against paramter definition with functions.
// Particularly the function takes in argument which is multi-dimentional.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Roland Kruse and Jie Xu.
// SPDX-License-Identifier: CC0-1.0

module test#(
    parameter SIZE = 4,
    parameter P = sum({32'h1,32'h2,32'h3,32'h4}, SIZE))

    (input clk,
     input logic sel,
     output [P:0] res);

    logic [P:0] cc = 'h45;

    assign res = sel ? cc : {(P+1){1'b1}};

    function integer sum;
        input [3:0][31:0] values;
        input int size;

        sum = 0;

        begin
            for (int i = 0; i < size; i ++)
                sum += values[i];
        end
    endfunction

endmodule
