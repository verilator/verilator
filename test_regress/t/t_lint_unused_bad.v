// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off UNOPTPUBLIC

module t;

  sub sub ();

endmodule

module sub;

  wire pub  /*verilator public*/;  // Ignore publics

  wire [5:0] assunu1 = 0;  // Assigned but unused

  wire [3:0] assunub2 = 0;  // Assigned but bit 2 unused

  wire [15:10] udrb2;  // [14:13,11] is undriven
  assign udrb2[15] = 0;
  assign udrb2[12] = 0;
  assign udrb2[10] = 0;

  wire unu3;  // Totally unused

  wire [3:0] mixed;  // [3] unused & undr, [2] unused, [1] undr, [0] ok
  assign mixed[2] = 0;
  assign mixed[0] = 0;

  wire [2:0] cmdln_off;  // Suppressed by command line
  assign cmdln_off = 0;

  localparam THREE = 3;

  parameter UNUSED_P = 1;
  localparam UNUSED_LP = 2;

  genvar unused_gv;
  genvar ok_gv;

  // verilator lint_off UNUSEDSIGNAL
  wire linter_sig1;
  localparam linter_param1 = 1;
  genvar linter_genvar1;
  // verilator lint_on UNUSEDSIGNAL

  // verilator lint_off UNUSEDPARAM
  wire linter_sig2;
  localparam linter_param2 = 2;
  genvar linter_genvar2;
  // verilator lint_on UNUSEDPARAM

  // verilator lint_off UNUSEDGENVAR
  wire linter_sig3;
  localparam linter_param3 = 3;
  genvar linter_genvar3;
  // verilator lint_on UNUSEDGENVAR

  // verilator lint_off UNUSED
  wire linter_sig4;
  localparam linter_param4 = 4;
  genvar linter_genvar4;
  // verilator lint_on UNUSED

  case (2)
    1: begin : named
      localparam BLOCK_PARAM = 10;
    end
    2: begin : named
      localparam BLOCK_PARAM = 20;
    end
    3: begin : named
      localparam BLOCK_PARAM = 30;
    end
  endcase

  initial begin
    if (0 && assunu1[0] != 0 && udrb2 != 0) begin
    end
    if (0 && assunub2[THREE] && assunub2[1:0] != 0) begin
    end
    if (0 && mixed[1:0] != 0) begin
    end
    if (named.BLOCK_PARAM != 20) $stop;
  end

  generate
    if (0) begin : gen_gv_if0
      for (ok_gv = 0; ok_gv < 1; ++ok_gv) begin : gen_gv_if0_for
      end
    end
  endgenerate

  class fields;
    int never_accessed;
    int only_written;
    int only_read;
    int initialized = 5;
  endclass

  initial begin
    automatic fields obj = new();
    obj.only_written = 2;
    $display("%0d %0d", obj.only_read, obj.initialized);
  end

  class partial_fields;
    bit [6:0] bit0;
    bit [6:0] read_all;
    bit [6:0] write_all;
    bit [6:0] mixed_bit0;
    bit [6:0] mixed_undriven;
    bit [8:2] part_range;
    bit [2:0][4:0] nested_range;
    bit [1:0][6:0] dynamic_range;
    bit [2:0] dynamic_index;
    bit [6:0] update_bit;

    function void touch();
      mixed_bit0[0] = 1'b1;
      $display("%h", mixed_bit0[0]);
    endfunction

    function void seed();
      mixed_undriven[0] = 1'b1;
    endfunction

    function bit [6:0] get_data();
      return mixed_undriven;
    endfunction
  endclass

  initial begin
    automatic partial_fields obj = new();
    obj.bit0[0] = 1'b1;
    $display("%h", obj.bit0[0]);
    obj.read_all[0] = 1'b1;
    $display("%h", obj.read_all);
    obj.write_all = '1;
    $display("%h", obj.write_all[0]);
    obj.touch();
    $display("%h", obj.mixed_bit0[0]);
    obj.mixed_undriven[0] = 1'b1;
    $display("%h", obj.get_data());
    obj.part_range[5:3] = '1;
    $display("%h", obj.part_range[5:3]);
    obj.nested_range[1][2:1] = '1;
    $display("%h", obj.nested_range[1][2:1]);
    obj.dynamic_index = 3'd1;
    obj.dynamic_range[1][obj.dynamic_index] = 1'b1;
    $display("%h", obj.dynamic_range[1][obj.dynamic_index]);
    obj.update_bit[0]++;
  end

  // Ordinary variables provide controls for the corresponding class field accesses.
  bit [6:0] module_bit0;
  bit [6:0] module_read_all;
  bit [6:0] module_write_all;
  bit [6:0] module_mixed_bit0;
  bit [6:0] module_mixed_undriven;
  bit [1:0][6:0] module_dynamic_range;
  bit [2:0] module_dynamic_index;

  function void touch();
    module_mixed_bit0[0] = 1'b1;
    $display("%h", module_mixed_bit0[0]);
  endfunction

  function void seed();
    module_mixed_undriven[0] = 1'b1;
  endfunction

  function bit [6:0] get_data();
    return module_mixed_undriven;
  endfunction

  initial begin
    module_bit0[0] = 1'b1;
    $display("%h", module_bit0[0]);
    module_read_all[0] = 1'b1;
    $display("%h", module_read_all);
    module_write_all = '1;
    $display("%h", module_write_all[0]);
    touch();
    $display("%h", module_mixed_bit0[0]);
    module_mixed_undriven[0] = 1'b1;
    $display("%h", get_data());
    module_dynamic_index = 3'd1;
    module_dynamic_range[1][module_dynamic_index] = 1'b1;
    $display("%h", module_dynamic_range[1][module_dynamic_index]);
  end

endmodule
