// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Risto Pejasinovic.
// SPDX-License-Identifier: CC0-1.0

module submod2 ();
endmodule

module submod #(
)();
    if(1) begin : submod_gen
        wire l1_sig;
        if(1) begin : nested_gen
            submod2 submod_nested();
        end
        submod2 submod_l1();
    end
    submod2 submod_l0();
endmodule

module test(
);
    genvar N;
    generate for(N=0; N<2; N=N+1)
        begin : FOR_GENERATE
            submod  submod_for();
            if(1) begin
                submod  submod_2();
            end
            submod  submod_3();
    end endgenerate
endmodule
