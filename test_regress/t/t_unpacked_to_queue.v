// DESCRIPTION: Verilator: Casting queues and dynamic arrays
// into queues as function arguments
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop()
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin \
    $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", \
    `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); \
    `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin \
    $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", \
    `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);


class check #(parameter WIDTH=8);
    static function automatic void check_array (int n,
                                    logic [WIDTH-1:0] array []);
        for (int r=0; r<n; r++) begin
            `checkh(array[r], WIDTH'(r))
        end
    endfunction

    static function automatic void check_string (int n,
                                    string array []);
        for (int r=0; r<n; r++) begin
            `checks(array[r], "test")
        end
    endfunction
endclass

module test();

    localparam NUM_ELEMS = 4;

    string       array_s  [NUM_ELEMS];

    logic [7:0]  array_8  [NUM_ELEMS];
    logic [15:0] array_16 [NUM_ELEMS];
    logic [31:0] array_32 [NUM_ELEMS];
    logic [63:0] array_64 [NUM_ELEMS];
    logic [95:0] array_96 [NUM_ELEMS];

    logic [7:0]  queue_8  [$];
    logic [15:0] queue_16 [$];
    logic [31:0] queue_32 [$];
    logic [63:0] queue_64 [$];
    logic [95:0] queue_96 [$];


    initial begin
        for (int i = 0; i < NUM_ELEMS; i++) begin
            array_s[i]  = "test";
            array_8[i]  = 8'(i);
            array_16[i] = 16'(i);
            array_32[i] = 32'(i);
            array_64[i] = 64'(i);
            array_96[i] = 96'(i);
            queue_8.push_back(8'(i));
            queue_16.push_back(16'(i));
            queue_32.push_back(32'(i));
            queue_64.push_back(64'(i));
            queue_96.push_back(96'(i));
        end

        check#(1)::check_string(NUM_ELEMS, array_s);

        check#(8)::check_array(NUM_ELEMS, array_8);
        check#(16)::check_array(NUM_ELEMS, array_16);
        check#(32)::check_array(NUM_ELEMS, array_32);
        check#(64)::check_array(NUM_ELEMS, array_64);
        check#(96)::check_array(NUM_ELEMS, array_96);

        check#(8)::check_array(NUM_ELEMS, queue_8);
        check#(16)::check_array(NUM_ELEMS, queue_16);
        check#(32)::check_array(NUM_ELEMS, queue_32);
        check#(64)::check_array(NUM_ELEMS, queue_64);
        check#(96)::check_array(NUM_ELEMS, queue_96);

        $display("All checks passed");
        $finish();
    end
endmodule
