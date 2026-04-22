// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Parameterized class with a type param depending on a value param.
// Covers #5479's original class-return domain alongside dependent-type
// resolution.

class C #(int W = 8, type T = logic [W-1:0]);
  T m_val;
  function T get(); return m_val; endfunction
endclass

module t;
  C #(8)  c8;
  C #(16) c16;
  C #(32) c32;

  initial begin
    c8  = new();
    c16 = new();
    c32 = new();

    c8.m_val  = 8'hA5;
    c16.m_val = 16'hBEEF;
    c32.m_val = 32'hDEADBEEF;

    if ($bits(c8.get()) !== 8) begin
      $write("%%Error $bits(c8.get())=%0d\n", $bits(c8.get())); $stop;
    end
    if (c8.get() !== 8'hA5) begin
      $write("%%Error c8.get()=%h\n", c8.get()); $stop;
    end

    if ($bits(c16.get()) !== 16) begin
      $write("%%Error $bits(c16.get())=%0d\n", $bits(c16.get())); $stop;
    end
    if (c16.get() !== 16'hBEEF) begin
      $write("%%Error c16.get()=%h\n", c16.get()); $stop;
    end

    if ($bits(c32.get()) !== 32) begin
      $write("%%Error $bits(c32.get())=%0d\n", $bits(c32.get())); $stop;
    end
    if (c32.get() !== 32'hDEADBEEF) begin
      $write("%%Error c32.get()=%h\n", c32.get()); $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
