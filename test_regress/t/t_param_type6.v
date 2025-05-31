// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface intf #(
    parameter type the_type = bit
);
    the_type foo;
endinterface

module t (/*AUTOARG*/
    // Inputs
    clk
    );

    input clk;

    intf #(.the_type (logic [7:0])) intf_eight();
    sub #(.type_bits (8)) sub_eight (.intf_pin (intf_eight));

    // finish report
    always @ (posedge clk) begin
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule

module sub #(
    parameter int type_bits
)(
    intf intf_pin
);

    localparam type intf_type = type(intf_pin.foo);
    initial begin
        if ($bits(intf_type) != type_bits) $stop();
    end

endmodule
