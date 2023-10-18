// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Josh Redford.
// SPDX-License-Identifier: CC0-1.0

interface my_if #(
    parameter integer DW = 8
) ();
    if (DW < 4) begin: gen_blk
        // under generate block, where V3Width won't process
        function automatic [DW-1:0] myfunc();
            return DW;
        endfunction
    end
endinterface


module t (
    my_if top_if
);
    // No other reference to the parameterizable interface 'my_if' here
endmodule
