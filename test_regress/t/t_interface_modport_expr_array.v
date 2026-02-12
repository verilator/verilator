// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Test modport expressions with arrayed interface instances (unsupported)

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface base_if;
  logic [7:0] wr;
  logic [7:0] rd;
  modport host(output wr, input rd);
  modport dev(input wr, output rd);
endinterface

interface container_if;
  base_if ch[2] ();

  // Modport expressions accessing arrayed interface instances
  modport mp(
      output .ch0_wr(ch[0].wr),
      input .ch0_rd(ch[0].rd),
      output .ch1_wr(ch[1].wr),
      input .ch1_rd(ch[1].rd)
  );
endinterface

module consumer (
    container_if.mp port
);
  // Access through modport expression virtual ports
  assign port.ch0_rd = port.ch0_wr + 8'h10;
  assign port.ch1_rd = port.ch1_wr + 8'h20;
endmodule

module top;
  container_if cont ();

  consumer m_cons (.port(cont));

  initial begin
    cont.ch[0].wr = 8'hA0;
    cont.ch[1].wr = 8'hB0;
    #1;
    `checkh(cont.ch[0].rd, 8'hB0);
    `checkh(cont.ch[1].rd, 8'hD0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
