// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

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
    $display("UVM Report %s:%d: %s %s", filename, line, id, message);
  endfunction : m__uvm_report_dpi
endpackage

module t;
  int i;
  string s;
  chandle h;

  // To cover testing cases, this has non-zero LSB/LO
  logic [31+8:8] exposed  /*verilator public*/;

  uvm_hdl_data_t lval;

  initial begin
    // TODO TEST:
    // extern const char* uvm_dpi_get_next_arg_c(int init);

    //===== Tool
    s = uvm_dpi_get_tool_name_c();
    $display("uvm_dpi_get_tool_name_c() = %s", s);
    `checks(s, "Verilator");

    s = uvm_dpi_get_tool_version_c();
    // - is so doesn't compare in .out file, in case version changes
    $display("- uvm_dpi_get_tool_version_c() = %s", s);
    if (s == "") $stop;

    //===== Regexp
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

    //===== Hier
`ifdef VERILATOR
`ifdef TEST_VERBOSE
    $c("Verilated::scopesDump();");
`endif
`endif

    $display("= uvm_hdl_check_path");
    i = uvm_hdl_check_path("t.__NOT_FOUND");
    `checkh(i, 0);
    i = uvm_hdl_check_path("t.exposed");
    `checkh(i, 1);
    i = uvm_hdl_check_path("$root.t.exposed");
    `checkh(i, 1);

    $display("= uvm_hdl_read simple variable");
    exposed = 32'hb001;
    lval = '0;  // Upper bits not cleared by uvm_hdl_read
    i = uvm_hdl_read("t.exposed", lval);
    `checkh(i, 1);
    `checkh(lval[31:0], exposed);

    lval = '0;
    $display("= uvm_hdl_read not found (bad)");
    $display("===\nUVM Report expected on next line:");
    i = uvm_hdl_deposit("t.__DEPOSIT_NOT_FOUND", lval);
    `checkh(i, 0);

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

    $display("= uvm_hdl_deposit bad ranges");
    $display("===\nUVM Report expected on next line:");
    i = uvm_hdl_deposit("t.exposed[10:3]", lval);
    `checkh(i, 0);
    $display("===\nUVM Report expected on next line:");
    i = uvm_hdl_deposit("t.exposed[99:15]", lval);
    `checkh(i, 0);

`ifdef VERILATOR
    // UNSUPPORTED: force/release via VPI
    // If support, validate or throw unsupported on force/release part-selects
    $display("= uvm_hdl_force");
    $display("===\nUVM Report expected on next line:");
    i = uvm_hdl_force("t.exposed", 62);
    `checkh(i, 0);

    $display("= uvm_hdl_release");
    $display("===\nUVM Report expected on next line:");
    i = uvm_hdl_release("t.exposed");
    `checkh(i, 0);

    $display("= uvm_hdl_release_and_read");
    $display("===\nUVM Report expected on next line:");
    i = uvm_hdl_release_and_read("t.exposed", lval);
    `checkh(i, 0);
`endif

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
