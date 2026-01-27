// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface iface;
   function static func;
   endfunction
endinterface

module t;
   initial begin
      iface::func();  // BAD
      $stop;
   end
endmodule
