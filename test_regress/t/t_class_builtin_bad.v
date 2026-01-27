// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
   function int rand_mode(bit onoff);
      return 1;
   endfunction
   function int constraint_mode(bit onoff);
      return 1;
   endfunction
endclass

module t;
   initial begin
      Cls c;
   end
endmodule
