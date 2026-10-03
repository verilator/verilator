// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Krzysztof Boronski
// SPDX-License-Identifier: CC0-1.0

int i = 0;

function int postincrement_i;
  return i++;
endfunction

module t;
  initial begin
    automatic int arr[3][3] = {{1, 2, 3}, {4, 5, 6}, {7, 8, 9}};
    i = 0;
    arr[postincrement_i()][postincrement_i()]++;
    $display("Value: %d", i);
  end

  bit clk;
  bus_if buses[2] (.clk);
  virtual bus_if vifs[2];

  initial begin
    vifs[0] = buses[0];
    vifs[1] = buses[1];
    // The interface is evaluated again to note the synchronous drive
    vifs[postincrement_i()].cb.w <= 1;
  end
endmodule

interface bus_if (
    input bit clk
);
  bit w;
  clocking cb @(posedge clk);
    output w;
  endclocking
endinterface
