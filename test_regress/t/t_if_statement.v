// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
  (/*AUTOARG*/
   // Inputs
   clk
   );

    input clk;
    int wordQ [$];
    logic[99:0] myint;
    int error_count = 0;
    initial begin
        // Ternary Example
        wordQ.push_back(100);
        myint = wordQ.size() > 0 ? 100'(wordQ.pop_front()) : 100'(99);

        if (myint != 100) begin
            error_count += 1;
            $display("Expected myint=%0d, not %0d", 100, myint);
        end

        // If statement Example
        wordQ.push_back(100);
        if (wordQ.size() > 0) begin
            myint = 100'(wordQ.pop_front());
        end else begin
            myint = 100'(99);
        end

        if (myint != 100) begin
            error_count += 1;
            $display("Expected myint=%0d, not %0d", 100, myint);
        end
        if (error_count != 0) begin
            $error("Encountered %0d errors", error_count);
        end
        $finish;
    end
endmodule
