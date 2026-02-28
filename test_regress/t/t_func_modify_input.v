// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

class foo;
   function void g(input integer x);
      f(x);
   endfunction
   function void f(inout integer x);
   endfunction
endclass
