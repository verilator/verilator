// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%p exp=%p\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package p;
  typedef enum logic [1:0] {
    A,
    B,
    C,
    D
  } e_t;
  typedef e_t alias_t;
  typedef enum logic signed [6:0] {
    NEG = -7,
    POS = 37
  } signed_t;
  typedef enum logic [64:0] {
    LO = 65'h1,
    HI = 65'h1_2345_6789_abcdef01
  } wide_t;
endpackage

class Producer;
  task get(input p::e_t value, output p::alias_t result);
    result = value;
  endtask
endclass

module t (
    input clk
);
  import p::*;
  logic [1:0] s;
  logic [1:0] values[4];
  logic [6:0] slice;
  logic signed [14:0] signed_value;
  logic [64:0] wide_value;
  logic [94:0] expanded_value;
  logic [32:0] truncated_value;
  e_t ev;
  alias_t alias_value;
  struct packed {logic [1:0] status;} packet;
  Producer producer = new;
  int cycle = 0;

  // The issue's original task output must convert from enum to logic, not vice versa.
  task automatic f(output e_t o);
    o = C;
  endtask

  task automatic get(input e_t value, output alias_t result);
    /*verilator no_inline_task*/
    result = value;
  endtask

  function automatic void get_function(input e_t value, output e_t result);
    result = value;
  endfunction

  task automatic get_signed(input signed_t value, output signed_t result);
    result = value;
  endtask

  task automatic get_wide(input wide_t value, output wide_t result);
    result = value;
  endtask

  task automatic next_value(inout e_t value);
    value = value.next();
  endtask

  task automatic set_ref(ref e_t value, input e_t source);
    value = source;
  endtask

  function automatic logic [1:0] read_value(input logic [1:0] value);
    return value;
  endfunction

  function automatic e_t read_ref(const ref alias_t value);
    return value;
  endfunction

  initial begin
    s = '0;
    f(s);
    `checkh(s, 2'd2);
  end

  always @(posedge clk) begin
    ev = e_t'(cycle);
    get(ev, s);
    `checkh(s, 2'(cycle));
    get(ev, alias_value);
    `checkh(alias_value, ev);
    producer.get(ev, packet.status);
    `checkh(packet.status, 2'(cycle));
    get_function(ev, values[cycle]);
    `checkh(values[cycle], 2'(cycle));
    slice = '1;
    get(ev, slice[4:3]);
    `checkh(slice, (7'h7f & ~(7'h3 << 3)) | (7'(cycle) << 3));
    get_signed(cycle[0] ? NEG : POS, signed_value);
    `checkh(signed_value, cycle[0] ? 15'(-7) : 15'(37));
    get_wide(cycle[0] ? HI : LO, wide_value);
    `checkh(wide_value, cycle[0] ? HI : LO);
    get_wide(cycle[0] ? HI : LO, expanded_value);
    `checkh(expanded_value, 95'(wide_value));
    get_wide(cycle[0] ? HI : LO, truncated_value);
    `checkh(truncated_value, 33'(wide_value));
    `checkh(read_value(ev), 2'(cycle));
    `checkh(read_ref(ev), ev);
    next_value(ev);
    `checkh(ev, 2'(cycle + 1));
    set_ref(ev, alias_value);
    `checkh(ev, alias_value);
    if (++cycle == 4) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
