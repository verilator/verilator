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
    typedef struct{
        logic [31:0] subarr[4];
    } arr_str_t;
    typedef struct {
        string txt;
        struct {
            logic m0;
            logic [3:0] m1;
            logic [7:0] arr[2][3];
            arr_str_t str[5];
        } sub;
    } struct_t;
    struct_t s1;
    struct_t s2;
    struct_t s3;

    assign {s1.sub.m0, s1.sub.m1} = {1'b0, 4'h5};
    assign {s2.sub.m0, s2.sub.m1} = {1'b0, 4'h5};
    assign s1.txt = "text";
    assign s2.txt = "text";

    assign {s1.sub.arr[0][0], s2.sub.arr[0][0]} = {8'h01, 8'h01};
    assign {s1.sub.arr[0][1], s2.sub.arr[0][1]} = {8'h02, 8'h02};
    assign {s1.sub.arr[0][2], s2.sub.arr[0][2]} = {8'h03, 8'h03};
    assign {s1.sub.arr[1][0], s2.sub.arr[1][0]} = {8'h04, 8'h04};
    assign {s1.sub.arr[1][1], s2.sub.arr[1][1]} = {8'h05, 8'h05};
    assign {s1.sub.arr[1][2], s2.sub.arr[1][2]} = {8'h06, 8'h06};

    assign {s3.sub.m0, s3.sub.m1} = {1'b0, 4'h5};
    assign s3.txt = "text";

    assign s3.sub.arr[0][0] = 8'h01;
    assign s3.sub.arr[0][1] = 8'h02;
    assign s3.sub.arr[0][2] = 8'h03;
    assign s3.sub.arr[1][0] = 8'h24; // One mismatch
    assign s3.sub.arr[1][1] = 8'h05;
    assign s3.sub.arr[1][2] = 8'h06;

    initial begin
        if(s3 == s1) $stop;
        if(s1 == s2 && s3 != s1) begin
            $write("*-* All Finished *-*\n");
            $finish;
        end else begin
            $fatal;
        end
    end
endmodule
