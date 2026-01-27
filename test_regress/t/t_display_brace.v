// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef int unsigned ahb_addr_t;
typedef int unsigned ahb_data_t;

class ahb_seq_item;
  ahb_addr_t address;
  ahb_data_t data[];

  function string to_string();
    string result_str, data_str;
    result_str = $sformatf(" addr=0x%0x ", address);
    data_str = " data=";
    if (data.size() == 0) data_str = {data_str, "-"};
    else if (data.size() == 1) data_str = {data_str, $sformatf("0x%0x", data[0])};
    else begin
      data_str = {data_str, $sformatf("%0d'{", data.size())};
      foreach (data[i]) data_str = {data_str, $sformatf(" 0x%0x", data[i])};
      data_str = {data_str, " }"};
    end
    result_str = {result_str, data_str};
    return result_str;
  endfunction

endclass


module top;

  initial begin
    ahb_seq_item tr;

    tr = new();
    tr.data = '{'h11, 'h22, 'h33, 'h44, 'h55, 'h66};
    $display(" tr(bytes, LE) @0x10: %0s", tr.to_string());

    $finish;
  end

endmodule
