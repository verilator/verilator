// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Johan Bjork.

interface intf;
    logic a;
    modport source(output a);
    modport sink(input a);
endinterface

module t
#(
    parameter N = 1
)
(   input [N-1:0] a_in,
    output[N-1:0] a_out
);
    intf ifs[N-1:0] ();
    logic   [N-1:0] a_q;

    assign a_out = a_q;
    assign ifs[0].a  = a_in[0];
    initial begin
       $write("*-* All Finished *-*\n");
       $finish;
    end
endmodule
