// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.

module secret_impl (
                    input  a,
                    input  oe,
                    inout  z,
                    output y);

   assign z = oe ? a : 1'bz;
   assign y = z;

endmodule
