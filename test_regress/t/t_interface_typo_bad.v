// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

//bug1097

interface foo_intf;
endinterface

module submod
  (
   foo_intf foo
   );

endmodule

module t (/*AUTOARG*/);
   // Intentional typo, compiler should point this out, or that fo_intf does
   // not match foo_intf on the submod port map
   fo_intf the_foo;

   submod
     submod_inst
       (
        .foo (the_foo)
        );

endmodule
