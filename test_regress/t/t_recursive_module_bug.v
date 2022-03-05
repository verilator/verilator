// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2022 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// This hits a case where parameter specialization of recursive modules
// used to yield a module list that was not topologically sorted, which
// then caused V3Inline to blow up as it assumes that.

module top #(
    parameter N=8
) (
    input   wire  [N-1:0] i,
    output  wire  [N-1:0] o,
    output  wire  [N-1:0] a
);

sub #(.N(N)) inst(.i(i), .o(a));

generate if (N > 1) begin: recursive
    top #(.N(N/2)) hi(.i(i[N   - 1:N/2]), .o(o[N   - 1:N/2]), .a());
    top #(.N(N/2)) lo(.i(i[N/2 - 1:  0]), .o(o[N/2 - 1:  0]), .a());
end else begin: base
    assign o = i;
end endgenerate

endmodule

module sub #(
    parameter N = 8
) (
    input   wire  [N-1:0] i,
    output  wire  [N-1:0] o
);

generate if (N > 1) begin: recursive
    sub #(.N(N/2)) hi(.i(i[N   - 1:N/2]), .o(o[N   - 1:N/2]));
    sub #(.N(N/2)) lo(.i(i[N/2 - 1:  0]), .o(o[N/2 - 1:  0]));
end else begin: base
    assign o = i;
end endgenerate

endmodule
