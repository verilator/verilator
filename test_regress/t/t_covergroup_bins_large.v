// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Array and automatic bins declarations of up to 1048576 bins, the limit of one
// declaration.  Their sample() code must not grow with their number of bins.

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [32:0] data33;
  logic [19:0] data20;
  logic [30:0] data31;
  logic signed [14:0] data15;

  // 1048576 automatic bins of 8192 values
  covergroup cg_auto;
    option.auto_bin_max = 1048576;
    coverpoint data33;
  endgroup

  // 1048576 single-value bins, over the whole domain
  covergroup cg_array;
    coverpoint data20 {
      bins b[] = {[0 : $]};
    }
  endgroup

  // 1000000 implicit automatic bins of 2147 values, the last also holding the remainder
  covergroup cg_implicit;
    option.auto_bin_max = 1000000;
    coverpoint data31;
  endgroup

  // Ignored values leave 16384 of the 32768 single-value bins without values
  covergroup cg_array_ignore;
    coverpoint data15 {
      bins b[] = {[-16384 : 16383]};
      ignore_bins neg = {[$ : -1]};
    }
  endgroup

  // 1000 automatic bins of 32 values, the last also holding the remainder: ignored
  // values leave the first 10 bins without values
  covergroup cg_auto_ignore;
    option.auto_bin_max = 1000;
    coverpoint data15 {
      ignore_bins low = {[$ : -16065]};
    }
  endgroup

  initial begin
    automatic cg_auto cga = new;
    automatic cg_array cgr = new;
    automatic cg_implicit cgi = new;
    automatic cg_array_ignore cgri = new;
    automatic cg_auto_ignore cgai = new;

    // Coverage is expected as get_inst_coverage() computes it: 100 * (covered / total)

    // Bin boundaries
    data33 = 0;
    cga.sample();
    data33 = 8191;
    cga.sample();
    `checkr(cga.get_inst_coverage(), 100.0 * (1.0 / 1048576));
    data33 = 8192;
    cga.sample();
    data33 = '1;
    cga.sample();
    `checkr(cga.get_inst_coverage(), 100.0 * (3.0 / 1048576));
    // Every bin
    for (int i = 0; i < 1048576; ++i) begin
      data33 = 33'(i) * 8192 + 33'((i * 7) % 8192);
      cga.sample();
    end
    `checkr(cga.get_inst_coverage(), 100.0);

    data20 = 0;
    cgr.sample();
    data20 = '1;
    cgr.sample();
    `checkr(cgr.get_inst_coverage(), 100.0 * (2.0 / 1048576));
    for (int i = 0; i < 1048576; ++i) begin
      data20 = 20'(i);
      cgr.sample();
    end
    `checkr(cgr.get_inst_coverage(), 100.0);

    data31 = 0;
    cgi.sample();
    data31 = 2146;
    cgi.sample();
    `checkr(cgi.get_inst_coverage(), 100.0 * (1.0 / 1000000));
    data31 = 2147;
    cgi.sample();
    data31 = 31'd2146997852;  // last value of bin 999998
    cgi.sample();
    `checkr(cgi.get_inst_coverage(), 100.0 * (3.0 / 1000000));
    data31 = 31'd2146997853;  // first value of the last bin
    cgi.sample();
    data31 = '1;  // in the remainder of the last bin
    cgi.sample();
    `checkr(cgi.get_inst_coverage(), 100.0 * (4.0 / 1000000));
    for (int i = 0; i < 1000000; ++i) begin
      data31 = 31'(i) * 2147 + 31'(i % 2147);
      cgi.sample();
    end
    `checkr(cgi.get_inst_coverage(), 100.0);

    data15 = -1;
    cgri.sample();
    `checkr(cgri.get_inst_coverage(), 0.0);
    data15 = 0;
    cgri.sample();
    data15 = 16383;
    cgri.sample();
    `checkr(cgri.get_inst_coverage(), 100.0 * (2.0 / 16384));
    for (int i = -16384; i < 16384; ++i) begin
      data15 = 15'(i);
      cgri.sample();
    end
    `checkr(cgri.get_inst_coverage(), 100.0);

    data15 = -16065;
    cgai.sample();
    `checkr(cgai.get_inst_coverage(), 0.0);
    data15 = -16064;  // first value of bin 10
    cgai.sample();
    data15 = 16383;  // in the remainder of the last bin
    cgai.sample();
    `checkr(cgai.get_inst_coverage(), 100.0 * (2.0 / 990));
    for (int i = -16384; i < 16384; ++i) begin
      data15 = 15'(i);
      cgai.sample();
    end
    `checkr(cgai.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
