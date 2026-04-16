// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`ifdef T_V2020_3_1
function void uvm_report_error(string a, string b);
  $display("uvm_report_error(\"%s\", \"%s\")", a, b);
endfunction

export "DPI-C" function uvm_polling_value_change_notify;
function void uvm_polling_value_change_notify(int sv_key);
endfunction
`endif

// verilator lint_off WIDTH
`include "dpi/uvm_dpi.svh"
// verilator lint_on WIDTH

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Undocumented DPI available version of uvm_report
// UVM declares without 'context'
package uvm_pkg;
  export "DPI-C" function m__uvm_report_dpi;
  function void m__uvm_report_dpi(int severity, string id, string message, int verbosity,
                                  string filename, int line);
    $display("UVM Report %s:%0d: %s %s", filename, line, id, message);
  endfunction
endpackage

module t;
  int i;
  string s;
  chandle h;

  // To cover testing cases, this has non-zero LSB/LO
  logic [31+8:8] exposed  /*verilator public*/  /*verilator forceable*/;
  logic not_exposed;
  logic exposed_not_forceable  /*verilator public*/;
  logic [31+8:8] exposedContinuously  /*verilator public*/  /*verilator forceable*/;
  assign exposedContinuously = 32'h0;

  real realSignal  /*verilator public*/  /*verilator forceable*/;
  string stringSignal  /*verilator public*/;

  logic [83:4] wide_dec  /* verilator public*/;
  // verilator lint_off ASCRANGE
  logic [4:83] wide_asc  /* verilator public*/;
  // verilator lint_on ASCRANGE

  logic [31:0] mem1d[1:2]  /* verilator public*/;
  logic [31:0] mem2d[1:2][3:4]  /* verilator public*/;

  uvm_hdl_data_t lval;

  task releaseExposedContinuously(input logic [31:0] din, output int i);
    // verilator no_inline_task
    i = uvm_hdl_release("t.exposedContinuously");
  endtask

  initial begin
    // TODO TEST:
    // extern const char* uvm_dpi_get_next_arg_c(int init);

    begin : t_exports
      uvm_pkg::m__uvm_report_dpi(1, "id", "message", 1, `__FILE__, `__LINE__);
    end

    begin : t_tool
      s = uvm_dpi_get_tool_name_c();
      $display("uvm_dpi_get_tool_name_c() = %s", s);
      `checks(s, "Verilator");

      s = uvm_dpi_get_tool_version_c();
      // - is so doesn't compare in .out file, in case version changes
      $display("- uvm_dpi_get_tool_version_c() = %s", s);
      if (s == "") $stop;
    end

    begin : t_regexp
      $display("= uvm_re");
      h = uvm_dpi_regcomp("a.*b");

      i = uvm_dpi_regexec(h, "__a_b__");
      `checkh(i, 0);
      i = uvm_dpi_regexec(h, "__a_z__");
      `checkh(i, 1);
      uvm_dpi_regfree(h);

      i = uvm_re_match("a.*b", "__a__b__");
      `checkh(i, 0);
      i = uvm_re_match("a.*b", "__a__z__");
      `checkh(i, 1);

      s = uvm_glob_to_re("a foo bar");
      `checks(s, "/^a foo bar$/");
    end

    begin : t_hier
`ifdef VERILATOR
      $c("Verilated::lastContextp()->fatalOnVpiError(false);");
`ifdef TEST_VERBOSE
      $c("Verilated::scopesDump();");
`endif
`endif
    end

    begin : t_uvm_hdl_check_path
      $display("= uvm_hdl_check_path");
      i = uvm_hdl_check_path("t.__NOT_FOUND");
      `checkh(i, 0);
      i = uvm_hdl_check_path("t.exposed");
      `checkh(i, 1);
      i = uvm_hdl_check_path("$root.t.exposed");
      `checkh(i, 1);
    end

    begin : t_simple
      $display("= uvm_hdl_read simple variable");
      exposed = 32'hb001;
      lval = '0;  // Upper bits not cleared by uvm_hdl_read
      i = uvm_hdl_read("t.exposed", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], exposed);

      $display("= uvm_hdl_deposit simple variable");
      lval = 1024'hab;
      i = uvm_hdl_deposit("t.exposed", lval);
      `checkh(i, 1);
      `checkh(exposed, 32'hab);

      $display("= uvm_hdl_read single bit");
      exposed = 32'habcd;
      lval = '0;  // Upper bits not cleared by uvm_hdl_read
      i = uvm_hdl_read("t.exposed[11]", lval);
      `checkh(i, 1);
      `checkh(lval[0], exposed[11]);

      $display("= uvm_hdl_deposit single bit");
      lval = 1024'h0;
      i = uvm_hdl_deposit("t.exposed[11]", lval);
      `checkh(i, 1);
      `checkh(exposed, 32'habc5);
    end

    begin : t_multibit
      $display("= uvm_hdl_read multi-bit");
      exposed = 32'habcd;
      lval = '0;  // Upper bits not cleared by uvm_hdl_read
      i = uvm_hdl_read("t.exposed[19:12]", lval);
      `checkh(i, 1);
      `checkh(lval[7:0], exposed[19:12]);

      $display("= uvm_hdl_deposit multi-bit");
      lval = 1024'h12;
      i = uvm_hdl_deposit("t.exposed[19:12]", lval);
      `checkh(i, 1);
      `checkh(exposed, 32'ha12d);

      $display("= uvm_hdl_read/deposit wide decending");
      wide_dec = 80'h1234_56789abc_dcba8765;
      lval = '0;  // Upper bits not cleared by uvm_hdl_read
      i = uvm_hdl_read("t.wide_dec[79:64]", lval);
      `checkh(i, 1);
      `checkh(lval[15:0], wide_dec[79:64]);
      lval = 1024'hffe;
      i = uvm_hdl_deposit("t.wide_dec[79:64]", lval);
      `checkh(i, 1);
      //                    .vvv_v......._........
      `checkh(wide_dec, 80'h10ff_e6789abc_dcba8765);

      $display("= uvm_hdl_read/deposit wide ascending");
      wide_asc = 80'h1234_56789abc_dcba8765;
      lval = '0;  // Upper bits not cleared by uvm_hdl_read
      i = uvm_hdl_read("t.wide_asc[64:79]", lval);
      `checkh(i, 1);
      `checkh(lval[15:0], wide_asc[64:79]);
      lval = 1024'hffe;
      i = uvm_hdl_deposit("t.wide_asc[64:79]", lval);
      `checkh(i, 1);
      //                    ...._........_...vvvv.
      `checkh(wide_asc, 80'h1234_56789abc_dcb0ffe5);
    end

    begin : memory_1d
      $display("= uvm_hdl_read/deposit 1D memory");
      i = uvm_hdl_check_path("t.mem1d[0]");
      `checkh(i, 0);
      i = uvm_hdl_check_path("t.mem1d[1]");
      `checkh(i, 1);
      i = uvm_hdl_check_path("t.mem1d[2]");
      `checkh(i, 1);
      i = uvm_hdl_check_path("t.mem1d[3]");
      `checkh(i, 0);
      mem1d[1] = 1;
      mem1d[2] = 2;
      lval = '0;  // Upper bits not cleared by uvm_hdl_read
      i = uvm_hdl_read("t.mem1d[2]", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], 2);
      lval = 1024'h200;
      i = uvm_hdl_deposit("t.mem1d[2]", lval);
      `checkh(i, 1);
      `checkh(mem1d[2], 32'h200);
    end

    begin : memory_2d
      $display("= uvm_hdl_read/deposit 2D memory");
      i = uvm_hdl_check_path("t.mem2d[0][2]");
      `checkh(i, 0);
      i = uvm_hdl_check_path("t.mem2d[1][3]");
      `checkh(i, 1);
      i = uvm_hdl_check_path("t.mem2d[2][4]");
      `checkh(i, 1);
      i = uvm_hdl_check_path("t.mem2d[2][5]");
      `checkh(i, 0);
      mem2d = '{'{13, 14}, '{23, 24}};
      lval = '0;  // Upper bits not cleared by uvm_hdl_read
      i = uvm_hdl_read("t.mem2d[2][3]", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], 23);
      lval = 1024'h2300;
      i = uvm_hdl_deposit("t.mem2d[2][3]", lval);
      `checkh(i, 1);
      `checkh(mem2d[2][3], 32'h2300);
    end

    begin : t_read_bad
      $display("= uvm_hdl_read empty name (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_read("", lval);
      `checkh(i, 0);

      $display("= uvm_hdl_read from real (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_read("t.realSignal", lval);
      `checkh(i, 0);

      $display("= uvm_hdl_read from string (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_read("t.stringSignal", lval);
      `checkh(i, 0);

    end

    begin : t_deposit_bad
      $display("= uvm_hdl_deposit bad ranges");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_deposit("t.exposed[10:3]", lval);
      `checkh(i, 0);
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_deposit("t.exposed[99:15]", lval);
      `checkh(i, 0);

      $display("= uvm_hdl_deposit empty name (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_deposit("", lval);
      `checkh(i, 0);

      $display("= uvm_hdl_deposit not found (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_deposit("t.__DEPOSIT_NOT_FOUND", 12);
      `checkh(i, 0);

      $display("= uvm_hdl_deposit to real (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_deposit("t.realSignal", 0);
      `checkh(i, 0);

      $display("= uvm_hdl_deposit to string (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_deposit("t.stringSignal", 0);
      `checkh(i, 0);

`ifdef VERILATOR
      $display("= uvm_hdl_deposit to not exposed (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_deposit("t.not_exposed", 12);
      `checkh(i, 0);
`endif
    end

    begin : t_force_release
      exposed = 32'h11223344;
      i = uvm_hdl_read("t.exposed", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], exposed);

      $display("= uvm_hdl_force");
      i = uvm_hdl_force("t.exposed", 62);
      `checkh(i, 1);
      exposed = 32'h0;  // should have no effect, since signal is being forced
      `checkh(exposed, 32'd62);

      $display("= uvm_hdl_release");
      i = uvm_hdl_release("t.exposed");
      `checkh(i, 1);
      // exposed is not assigned continuously, so return value is force value
      `checkh(exposed, 32'd62);
      exposed = 32'hFFFF_FFFF;
      `checkh(exposed, 32'hFFFF_FFFF);

      $display("= uvm_hdl_release_and_read");
      exposed = 32'hFFFF_FFFF;
      force exposed[31+8:8] = 32'h0;
      lval = 1024'hFFFF_FFFF;
      i = uvm_hdl_release_and_read("t.exposed", lval);
      `checkh(i, 1);
      // exposed is not assigned continuously, so return value is force value
      `checkh(lval[31:0], 32'h0);
      `checkh(exposed, 32'h0);

    end

    begin : t_force_release_continuous
      $display("= uvm_hdl_force continuously assigned signal");
      i = uvm_hdl_force("t.exposedContinuously", 62);
      `checkh(i, 1);
      `checkh(exposedContinuously, 32'd62);

      force exposedContinuously = 32'hFFFF_FFFF;
      $display("= uvm_hdl_release continuously assigned signal");
      releaseExposedContinuously(
          exposedContinuously,
          i);  // Need to wrap VPI call in task for Verilation to actually check the release value
      `checkh(i, 1);
      `checkh(exposedContinuously, 32'h0);

      $display("= uvm_hdl_release_and_read continuously assigned signal");
      force exposedContinuously[31+8:8] = 32'hFFFF_FFFF;
      lval = 1024'hFFFF_FFFF;
      i = uvm_hdl_release_and_read("t.exposedContinuously", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], 32'h0);
      `checkh(t.exposedContinuously, 32'h0);

    end

    begin : t_force_partial
      // Partial force from SystemVerilog
      $display("= uvm_hdl_read partially forced signal");
      force exposed[15+8:8] = 16'h0;
      exposed = 32'hFFFF_FFFF;  // Expect 16 LSBs to stay at 0
      `checkh(exposed, 32'hFFFF_0000);
      lval = 1024'hAAAA_AAAA;
      i = uvm_hdl_read("t.exposed", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], exposed);

      $display("= uvm_hdl_release partially forced signal");
      i = uvm_hdl_release("t.exposed");
      `checkh(i, 1);
      `checkh(exposed, 32'hFFFF_0000);
      exposed = 32'hFFFF_FFFF;
      `checkh(exposed, 32'hFFFF_FFFF);

      // Partial force through UVM
      $display("= uvm_hdl_force multi-bit");
      i = uvm_hdl_force("t.exposed[23:8]", 0);  // [15+8:8] is not valid syntax in Verilator
      `checkh(i, 1);
      exposed = 32'hFFFF_FFFF;  // Expect 16 LSBs to stay at 0
      `checkh(exposed, 32'hFFFF_0000);

      $display("= uvm_hdl_release_and_read partially forced signal");
      lval = 1024'h0;
      i = uvm_hdl_release_and_read("t.exposed", lval);
      `checkh(i, 1);
      // exposed is not assigned continuously, so return value is force value
      `checkh(lval[31:0], 32'hFFFF_0000);
      `checkh(exposed, 32'hFFFF_0000);
      exposed = 32'hFFFF_FFFF;
      `checkh(exposed, 32'hFFFF_FFFF);
    end

    begin : t_force_partial_continuous
      $display("= uvm_hdl_force multi-bit continuously assigned signal");
      i = uvm_hdl_force("t.exposedContinuously[23:8]", 'hFFFF);
      `checkh(i, 1);
      `checkh(exposedContinuously, 32'h0000_FFFF);

      $display("= uvm_hdl_release partially forced continuously assigned signal");
      i = uvm_hdl_release("t.exposedContinuously");
      `checkh(i, 1);
      `checkh(exposedContinuously, 32'h0000_0000);

      $display("= uvm_hdl_release_and_read partially forced continuously assigned signal");
      force exposedContinuously[23:8] = 16'hFFFF;
      lval = 1024'h0;
      i = uvm_hdl_release_and_read("t.exposedContinuously", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], 32'h0000_0000);
      `checkh(exposedContinuously, 32'h0000_0000);
    end

    begin : t_force_single_bit
      $display("= uvm_hdl_force single bit");
      exposed = 32'hAAAA_AAAA;
      i = uvm_hdl_force("t.exposed[16]", 1);
      `checkh(i, 1);
      exposed = 32'h0;  // should have no effect on bit 16
      `checkh(exposed, 32'h0000_0100);

      $display("= uvm_hdl_release_and_read single bit");
      lval = 1024'h0;
      i = uvm_hdl_release_and_read("t.exposed[16]", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], 32'h0000_0001);
      exposed = 32'hFFFF_FFFF;
      `checkh(exposed, 32'hFFFF_FFFF);

      $display("= uvm_hdl_force single bit on continuously assigned signal");
      i = uvm_hdl_force("t.exposedContinuously[16]", 1);
      `checkh(i, 1);
      `checkh(exposedContinuously, 32'h0000_0100);

      $display("= uvm_hdl_release_and_read single bit on continuously assigned signal");
      lval = 1024'h0;
      i = uvm_hdl_release_and_read("t.exposedContinuously[16]", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], 32'h0000_0000);
      `checkh(exposedContinuously, 32'h0);
    end

    begin : t_partial_release
      $display("= uvm_hdl_release_and_read lower 16 bits only");
      force exposed = 32'h5555_5555;
      lval = 1024'h0;
      i = uvm_hdl_release_and_read("t.exposed[23:8]", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], 32'h0000_5555);
      exposed = 32'hFFFF_FFFF;
      `checkh(exposed, 32'h5555_FFFF);
      release exposed;

      $display("= uvm_hdl_release upper 16 bits only of continuously assigned signal");
      force exposedContinuously = 32'h5555_5555;
      lval = 1024'h0;
      i = uvm_hdl_release_and_read("t.exposedContinuously[39:24]", lval);
      `checkh(i, 1);
      `checkh(lval[31:0], 32'h0000_0000);
      `checkh(exposedContinuously, 32'h0000_5555);
      release exposedContinuously;
    end

    begin : t_force_bad
      $display("= uvm_hdl_force to not exposed (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_force("t.not_exposed", 12);
      `checkh(i, 0);

      $display("= uvm_hdl_force to not forcable (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_force("t.exposed_not_forceable", 12);
      `checkh(i, 0);

      $display("= uvm_hdl_force to real (bad)");
      $display("===\nUVM Report expected on next line:");
      i = uvm_hdl_force("t.realSignal", 0);
      `checkh(i, 0);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
