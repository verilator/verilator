// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2022 Jomit626
// SPDX-License-Identifier: CC0-1.0

`ifndef WIDTH
`define WIDTH 128
`endif

class item;
    bit [`WIDTH-1:0] data;
endclass

module t ();
    logic [`WIDTH-1:0] data;
    item item0 = new;

    initial begin
        item0.data = `WIDTH'hda7ada7a;
        data = item0.data;

        if (data != `WIDTH'hda7ada7a)
            $stop();

        $write("*-* All Finished *-*\n");
        $finish();
    end
endmodule
