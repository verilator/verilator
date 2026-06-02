// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Ref args with a packed-array range-direction mismatch must be accepted.
// IEEE 1800-2023 7.6: packed types are equivalent by bit width, not range
// direction, so [15:0] and [0:15] are compatible for a ref port.

module t;
  function void fill_desc(ref logic [3:0][7:0] arr);
    arr = 32'hdead_beef;
  endfunction

  function void fill_asc(ref logic [0:3][7:0] arr);
    arr = 32'hdead_beef;
  endfunction

  // Inner (basic-dtype) range-direction mismatch.
  function void fill_inner_desc(ref logic [1:0][15:0] arr);
    arr = 32'hdead_beef;
  endfunction

  function void fill_inner_asc(ref logic [1:0][0:15] arr);
    arr = 32'hdead_beef;
  endfunction

  logic [3:0][7:0]  a;   // descending outer
  logic [0:3][7:0]  b;   // ascending outer
  logic [1:0][15:0] c;   // descending inner
  logic [1:0][0:15] d;   // ascending inner

  int errors = 0;

  initial begin
    // Outer-dimension direction mismatch
    a = '0; fill_desc(a);        if (a !== 32'hdead_beef) errors++;
    b = '0; fill_desc(b);        if (b !== 32'hdead_beef) errors++;
    a = '0; fill_asc(a);         if (a !== 32'hdead_beef) errors++;
    b = '0; fill_asc(b);         if (b !== 32'hdead_beef) errors++;
    // Inner-dimension direction mismatch
    c = '0; fill_inner_desc(c);  if (c !== 32'hdead_beef) errors++;
    d = '0; fill_inner_desc(d);  if (d !== 32'hdead_beef) errors++;
    c = '0; fill_inner_asc(c);   if (c !== 32'hdead_beef) errors++;
    d = '0; fill_inner_asc(d);   if (d !== 32'hdead_beef) errors++;

    $display("a=%h b=%h c=%h d=%h errors=%0d", a, b, c, d, errors);
    if (errors == 0) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end else begin
      $stop;
    end
  end
endmodule
