// DESCRIPTION: Verilator: Verilog Test module
//
// Use this file as a template for submitting bugs, etc.
// This module takes a single clock input, and should either
//      $write("*-* All Finished *-*\n");
//      $finish;
// on success, or $stop.
//
// The code as shown applies a random vector to the Test
// module, then calculates a CRC on the Test module's outputs.
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
    typedef struct {
        string txt;
        struct {
            logic m0;
            logic [3:0] m1;
        } sub;
        logic [7:0] arr[2];
    } struct_t;
    struct_t s1;
    struct_t s2;

    assign {s1.sub.m0, s1.sub.m1} = {1'b0, 4'h5};
    assign {s2.sub.m0, s2.sub.m1} = {1'b0, 4'h5};
    assign s1.txt = "text";
    assign s2.txt = "text";
    assign s1.arr[0] = 8'h77;
    assign s2.arr[0] = 8'h77;
    assign s1.arr[1] = 8'h33;
    assign s2.arr[1] = 8'h33;

    initial begin
        if(s1 != s2) begin
            $fatal;
        end
        if(s1 == s2) begin
            $write("*-* All Finished *-*\n");
            $finish;
        end else begin
            $fatal;
        end
    end
endmodule
