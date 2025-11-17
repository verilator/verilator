// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Jonathan Drolet.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package config_pkg;
  typedef struct {
    int UPPER0;
    struct {
      int USE_QUAD0;
      int USE_QUAD1;
      int USE_QUAD2;
    } mac;
    int UPPER2;
  } config_struct_t;

endpackage

module t;
  import config_pkg::*;

  // Constant value unpacked struct support is limited at the moment.
  // Only localparams are supported, returning constant unpacked structure
  // from function or passing unpacked structure as parameters is not
  // (yet) supported
  localparam config_struct_t MY_CONFIG = '{
      UPPER0: 10,
      mac: '{USE_QUAD0: 4, USE_QUAD1: 5, USE_QUAD2: 6},
      UPPER2: 20
  };

  initial begin
    `checkd(MY_CONFIG.UPPER0, 10);
    `checkd(MY_CONFIG.mac.USE_QUAD0, 4);
    `checkd(MY_CONFIG.mac.USE_QUAD1, 5);
    `checkd(MY_CONFIG.mac.USE_QUAD2, 6);
    `checkd(MY_CONFIG.UPPER2, 20);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
