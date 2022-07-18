// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2022 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module top(
  input wire a,
  input wire b,
  output wire o
);

  logic [255:0] array [1:0];
  logic [255:0] tmp [1:0];

  // Nonsensical, but needs to compile. (In some real designs we can end up
  // with combinational loops via unpacked arrays)
  always_comb begin
    tmp[0] = array[a];
  end

  always_comb begin
    array[b] = tmp[0];
  end

  assign o = array[0][0];

endmodule
