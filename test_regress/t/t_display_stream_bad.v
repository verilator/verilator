// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  int value = 1;
  int other = 2;
  int result;
  bit flag;

  function automatic int passthrough(input int arg);
    return arg;
  endfunction

  initial begin
    result = passthrough({<<{value}});
    result = {<<{value}} + 1;
    result = value + {<<{value}};
    result = value[0] ? {<<{value}} : other;
    result = {{<<{value}}};
    flag = ({<<{value}} == other);
    $display({<<{value}});
    $display("%0d", {<<{value}});
    void'($sformatf("%0d", {<<{value}}));
    result = passthrough({<<{value}} + 1);
    result = int'({<<{value}});
    result = int'({<<{value}}) + 1;
  end
endmodule
