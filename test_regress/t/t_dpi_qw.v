// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

    wire [39:0] out;
    sub a(.value(out));

   import "DPI-C" context function void poke_value(input int i);


   initial begin
       poke_value(32'hdeadbeef);
       if (out !== 40'hdeadbeef) begin
          $display("[%0t] %%Error: t_dpi_qw: failed", $time);
          $stop;
       end

       $write("*-* All Finished *-*\n");
       $finish;
   end

endmodule

module sub(value);
    parameter WIDTH = 40;

    output [WIDTH-1:0] value;

    reg [WIDTH-1:0] value;

    task set_value(input bit [WIDTH-1:0] v);
        value = v;
    endtask

    export "DPI-C" task set_value;
endmodule
