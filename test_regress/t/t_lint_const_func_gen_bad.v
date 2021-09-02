// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Donald Owen.
// SPDX-License-Identifier: CC0-1.0

module t ();
   if (1) begin: GenConstFunc
      // IEEE 1800-2017 13.4.3, constant functions shall not be declared inside a
      //generate block
      function automatic bit constFunc();
         constFunc = 1'b1;
      endfunction

      localparam PARAM = constFunc();
    end
endmodule
