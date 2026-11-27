// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;
  wire [11:0] din = crc[11:0];
  logic [11:0] dout;

  // Streams connected to queue ports: the input is zero-filled to whole bytes, the output takes
  // the leftmost bits
  sub u_sub (
      .iq({>>byte{din}}),
      .oq({>>{dout}})
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    `checkh(dout, din);
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sub (
    input byte unsigned iq[$],
    output byte unsigned oq[$]
);
  assign oq = iq;
endmodule
