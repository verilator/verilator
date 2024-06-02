// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface Bus;
   logic [15:0] data;
endinterface

module t;
   Bus intf();
   virtual Bus vif = intf;

   function logic write_data(output logic[15:0] data);
      data = 'hdead;
      return 1;
   endfunction

   // verilator lint_off INFINITELOOP
   initial begin
      if (write_data(vif.data)) $write("dummy op");
      while (write_data(vif.data));
      for (int i = 0; write_data(vif.data); i += int'(write_data(vif.data)));
      for (int i = 0; write_data(vif.data++); i++);
   end

endmodule
