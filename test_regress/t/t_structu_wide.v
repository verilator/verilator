// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Jomit626.
// SPDX-License-Identifier: CC0-1.0

`ifndef WIDE_WIDTH
`define WIDE_WIDTH 128
`endif

module t ();
    typedef struct {
        bit [`WIDE_WIDTH-1:0] data;
    } wide_t;

    logic [`WIDE_WIDTH-1:0] ldata;
    wide_t wide_0;

    initial begin
        wide_0.data = `WIDE_WIDTH'hda7ada7a;
        ldata = wide_0.data;

        if (ldata != `WIDE_WIDTH'hda7ada7a)
            $stop();

        $write("*-* All Finished *-*\n");
        $finish();
    end
endmodule
