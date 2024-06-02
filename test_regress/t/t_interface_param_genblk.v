// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

// See #4664

interface intf #(
    parameter A = 10
);
    localparam B = A / A + 1; // 2

    logic [A/10-1:0] sig;
endinterface

module t;
    intf #(
        .A(100)
    ) intf();

    sub i_sub (
        .intf
    );
endmodule

module sub (
    intf intf
);

    if (intf.A == 10) begin
        $error("incorrect");
    end else if (intf.A / intf.B == 50) begin
    // end else if (intf.A / $bits(intf.sig) == 10) begin // TODO: support this
        $info("correct");
    end else begin
        $error("incorrect");
    end

    for (genvar i = intf.A - 2; i < intf.A + 1; i += intf.B) begin
        for (genvar j = intf.B; j > intf.A - 100; j--) begin
            if (i < intf.A - 2) $error("error");
            if (i > intf.A)     $error("error");
            $info("i = %0d, j = %0d", i, j);
        end
    end

    case (intf.A)
        10, intf.A - 10: $error("incorrect");
        intf.B * 50:     $info("correct");
        30:              $error("incorrect");
        default:         $error("incorrect");
    endcase
endmodule
