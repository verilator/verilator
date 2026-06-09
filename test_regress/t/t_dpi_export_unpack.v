// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// 9-Jun-2026: Modifications for this test contributed by Yilin Li.

export "DPI-C" task readHEX;
export "DPI-C" task loadHEX;

task readHEX;
  input string file;
  output logic [7:0] stimuli[32'h00010000];
  $readmemh(file, stimuli);
endtask

task loadHEX;
  input string file;
  logic [7:0] stimuli[32'h00010000];
  readHEX(file, stimuli);
endtask

module tb();

  logic [7:0] result[32'h00010000];
  initial begin
    loadHEX("dummy");
  end

endmodule