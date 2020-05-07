// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Matt Myers.
// SPDX-License-Identifier: CC0-1.0

`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

package config_pkg;
   typedef struct packed {
      int 	  UPPER0;
      struct 	  packed {
         int 	  USE_QUAD0;
         int 	  USE_QUAD1;
         int 	  USE_QUAD2;
      } mac;
      int 	  UPPER2;
   } config_struct;

   function automatic config_struct static_config(int selector);
      config_struct return_config;
      return_config = '0;
      return_config.UPPER0 = 10;
      return_config.UPPER2 = 20;
      return_config.mac.USE_QUAD0 = 4;
      return_config.mac.USE_QUAD2 = 6;
      case (selector)
        1: return_config.mac.USE_QUAD1 = 5;
      endcase
      return return_config;
   endfunction
endpackage : config_pkg

module t;
    import config_pkg::*;

    localparam config_struct MY_CONFIG = static_config(1);

    struct_submodule #(.MY_CONFIG(MY_CONFIG)) a_submodule_I ();
endmodule : t

module struct_submodule
  import config_pkg::*;
   #(parameter config_struct MY_CONFIG = '0);

   initial begin
      `checkd(MY_CONFIG.UPPER0, 10);
      `checkd(MY_CONFIG.mac.USE_QUAD0, 4);
      `checkd(MY_CONFIG.mac.USE_QUAD1, 5);
      `checkd(MY_CONFIG.mac.USE_QUAD2, 6);
      `checkd(MY_CONFIG.UPPER2, 20);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule : struct_submodule
