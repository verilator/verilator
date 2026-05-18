// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%h' exp='%h'\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0);
module t;
  logic clk;
  int i_header;
  int i_len;
  int i_data;
  int i_crc;

  int o_header;
  int o_len;
  int o_data;
  int o_crc;

  pkt_if pkt_if_init (clk);
  //this will not compile without -fno-life
  initial begin
    byte byte_pkt[$];

    //---------------------- STREAM WITH INTERFACE -------------------
    //using this forces verilator to a AstSel Node into a Stream Node
    #0 //make sure we dont optimize it all away in v3life
    pkt_if_init.s.extra = 8'hd;
    byte_pkt = {>>{pkt_if_init.s.extra}};
    if(8'hd == {>>{byte_pkt}}) begin
        $write("*-* All Finished *-*\n");
        $finish();
    end

  end

endmodule

interface pkt_if (
    input wire clk
);

    typedef struct packed {
        logic [31:0] extra;
        logic [31:0] empty;
        logic [31:0] data;
        logic valid;
        logic sop;
        logic eop;
    } avst_s;

    avst_s s;
    logic ready;

    // Read-Only Helper Signals
    logic sop_pulse;
    logic eop_pulse;

    modport src (
        output s,
        input ready,
        input sop_pulse, eop_pulse
    );

    modport snoop (
        input s,
        input ready,
        input sop_pulse, eop_pulse
    );

    modport sink (
        input s,
        output ready,
        input sop_pulse, eop_pulse
    );

endinterface