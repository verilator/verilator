// DESCRIPTION: Verilator: Verilog Test module
//
// Use this file as a template for submitting bugs, etc.
// This module takes a single clock input, and should either
//      $write("*-* All Finished *-*\n");
//      $finish;
// on success, or $stop.
//
// The code as shown applies a random vector to the Test
// module, then calculates a CRC on the Test module's outputs.
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by ____YOUR_NAME_HERE____.

module t (/*AUTOARG*/);

    typedef logic [3:0] foo_t;

    foo_t foo_s;

    assign bar_s = {foo_s, foo_s}.f1;

endmodule
