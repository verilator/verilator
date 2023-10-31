// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

/// Test for bug4553

// bit0: 'new' called
// bit1: 'myfunc' called
// bit2: 'myfunc' in class called
int calls = 0;

module t;
    // int calls = 0;  // TODO: Error: Internal Error: Can't locate varref scope

    function void myfunc();
        calls |= 32'b10;
    endfunction : myfunc

    class Cls #(int A = 0);
        function new();
            calls |= 32'b1;
        endfunction : new
        function void myfunc();
            calls |= 32'b100;
        endfunction : myfunc
    endclass

    Cls #(100) cls;

    // this block is following the definition of Cls
    initial begin
        cls = new;
        myfunc();

        if (calls != 32'b011) begin
            $write("calls: %0b\n", calls);
            $stop;
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
