// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(g,e) do if ((g) !== (e)) begin $write("%%Error: %s:%0d: got=%x exp=%x\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)
// verilog_format: on

module t;
  int a[1]  /* verilator forceable */ = '{0};
  int b[1];
  int old_value;
  typedef bit [6:0] narrow_t[3:1];
  typedef bit [64:0] wide_t[2:3];
  typedef bit [20:0] narrow_packed_t;
  typedef bit [129:0] wide_packed_t;
  narrow_t narrow_array  /* verilator forceable */;
  narrow_t narrow_source;
  wide_t wide_array  /* verilator forceable */;
  wide_t wide_source;
  narrow_packed_t narrow_expected;
  narrow_packed_t narrow_sampled;
  wide_packed_t wide_expected;
  wide_packed_t wide_sampled;
  bit [64:0] force_value;

  initial begin
    // A whole-array write must not overwrite the value captured in the Preponed region.
    b[0] = 7;
    #1;
    a = b;
    old_value = $sampled(int'({>>{a}}));
    `checkh(old_value, 0);
    old_value = int'({>>{a}});
    `checkh(old_value, 7);

    for (int cycle = 0; cycle < 6; ++cycle) begin
      foreach (narrow_source[i]) narrow_source[i] = 7'(cycle * 13 + i);
      foreach (wide_source[i]) begin
        wide_source[i] = 65'h1_1234_5678_9abc_def0 ^ 65'(cycle * 7 + i);
      end
      force_value = 65'h1_fedc_ba98_7654_3210 ^ 65'(cycle);
      if (cycle == 2) begin
        force narrow_array[2] = force_value[6:0];
        force wide_array[3] = force_value;
      end
      if (cycle == 4) begin
        release narrow_array[2];
        release wide_array[3];
      end
      #1;
      narrow_expected = {>>{narrow_array}};
      wide_expected = {>>{wide_array}};
      narrow_array = narrow_source;
      wide_array = wide_source;
      narrow_sampled = $sampled(narrow_packed_t'({>>{narrow_array}}));
      wide_sampled = $sampled(wide_packed_t'({>>{wide_array}}));
      `checkh(narrow_sampled, narrow_expected);
      `checkh(wide_sampled, wide_expected);

      // Repeated reads share the sample and must stay stable after another write.
      narrow_array = '{default: '0};
      wide_array = '{default: '0};
      narrow_sampled = $sampled(narrow_packed_t'({>>{narrow_array}}));
      wide_sampled = $sampled(wide_packed_t'({>>{wide_array}}));
      `checkh(narrow_sampled, narrow_expected);
      `checkh(wide_sampled, wide_expected);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
