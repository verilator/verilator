// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2014 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;
  reg [63:0] crc;
  reg [63:0] sum;

  parameter NPAD = 4;

  tri pad[NPAD-1:0];  // Array
  wire [NPAD-1:0] data0 = crc[0+:4];
  wire [NPAD-1:0] data1 = crc[8+:4];
  wire [NPAD-1:0] en = crc[16+:4];

  for (genvar g = 0; g < NPAD; ++g) begin : gpad
    Pad pad1 (
        .pad(pad[g]),
        .ena(en[g]),
        .data(data1[g])
    );
    Pad pad0 (
        .pad(pad[g]),
        .ena(!en[g]),
        .data(data0[g])
    );
  end

  // Each constant-index driver should resolve only its own element, even on a large array.
  wire [6:0] large_pad [3:129];
  for (genvar i = 3; i <= 129; ++i) begin
    wire enable = crc[i % 64];
    wire [6:0] value = 7'(crc >> (i % 57)) ^ 7'(i);
    assign large_pad[i] = enable ? value : 7'bz;
    assign large_pad[i] = enable ? 7'bz : ~value;
    always @(negedge clk) begin
      if (cyc > 1) `checkh(large_pad[i], enable ? value : ~value);
    end
  end

  // GPIO array ports must preserve each element through the IOBUF hierarchy.
  for (genvar cfg = 0; cfg < 2; ++cfg) begin : gpio_config
    localparam NumGPIOs = cfg == 0 ? 4 : 7;
    wire p_gpio [NumGPIOs];
    wire do_gpio [NumGPIOs];
    wire di_gpio [NumGPIOs];
    wire do_gpio_hiz [NumGPIOs];
    wire p_gpio_array [NumGPIOs];
    wire di_gpio_array [NumGPIOs];
    GPIO_iop #(.NumGPIOs(NumGPIOs)) gpio (
        .p_gpio(p_gpio),
        .do_gpio(do_gpio),
        .di_gpio(di_gpio),
        .do_gpio_hiz(do_gpio_hiz)
    );
    GPIONGeneralPurposeIOs_216_iop #(.USERPARAM_NumGPIOs(NumGPIOs)) gpio_array (
        .p_gpio(p_gpio_array),
        .do_gpio(do_gpio),
        .di_gpio(di_gpio_array),
        .do_gpio_hiz(do_gpio_hiz)
    );
    for (genvar i = 0; i < NumGPIOs; ++i) begin : gpio_pin
      assign do_gpio[i] = crc[i];
      assign do_gpio_hiz[i] = crc[i + 16];
      assign p_gpio[i] = do_gpio_hiz[i] ? ~crc[i] : 1'bz;
      assign p_gpio_array[i] = do_gpio_hiz[i] ? ~crc[i] : 1'bz;
      always @(negedge clk) begin
        if (cyc > 0) begin
          `checkh(p_gpio[i], crc[i + 16] ? ~crc[i] : crc[i]);
          `checkh(di_gpio[i], crc[i + 16] ? ~crc[i] : crc[i]);
          `checkh(p_gpio_array[i], crc[i + 16] ? ~crc[i] : crc[i]);
          `checkh(di_gpio_array[i], crc[i + 16] ? ~crc[i] : crc[i]);
        end
      end
    end
  end

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    sum <= {60'h0, pad[3], pad[2], pad[1], pad[0]} ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
    if (cyc == 0) begin
      // Setup
      crc <= 64'h5aef0c8d_d70a4497;
      sum <= 64'h0;
    end
    else if (cyc < 10) begin
      sum <= 64'h0;
    end
    else if (cyc < 90) begin
    end
    else if (cyc == 99) begin
      $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
      if (crc !== 64'hc77bb9b3784ea091) $stop;
      // What checksum will we end up with (above print should match)
      `define EXPECTED_SUM 64'he09fe6f2dfd7a302
      if (sum !== `EXPECTED_SUM) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Pad (
    inout pad,
    input ena,
    input data
);
  assign pad = ena ? data : 1'bz;
endmodule

module GPIO_iop #(
    parameter NumGPIOs = 4
) (
    inout p_gpio [NumGPIOs],
    input do_gpio [NumGPIOs],
    output di_gpio [NumGPIOs],
    input do_gpio_hiz [NumGPIOs]
);
  for (genvar i = 0; i < NumGPIOs; ++i) begin : Gen_gpio_0
    IOBUF gpio (.T(do_gpio_hiz[i]), .I(do_gpio[i]), .O(di_gpio[i]), .IO(p_gpio[i]));
  end
endmodule

module GPIONGeneralPurposeIOs_216_iop #(
    parameter USERPARAM_NumGPIOs = 4
) (
    inout p_gpio [USERPARAM_NumGPIOs],
    input do_gpio [USERPARAM_NumGPIOs],
    output di_gpio [USERPARAM_NumGPIOs],
    input do_gpio_hiz [USERPARAM_NumGPIOs]
);
  IOBUF gpio [USERPARAM_NumGPIOs] (.T(do_gpio_hiz), .I(do_gpio), .O(di_gpio), .IO(p_gpio));
endmodule

module IOBUF (
    input T,
    input I,
    output O,
    inout IO
);
  assign IO = T ? 1'bz : I;
  assign O = IO;
endmodule
