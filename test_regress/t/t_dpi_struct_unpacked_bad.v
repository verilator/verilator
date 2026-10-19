// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef union {
    int i;
    byte b;
  } union_t;
  typedef struct {int q[$];} queue_t;
  typedef struct {
    int i;
    union_t u[2];
  } with_union_t;
  typedef struct {event e;} event_t;

  // Members of types DPI does not allow
  import "DPI-C" function void i_queue(input queue_t s);
  import "DPI-C" function void i_union(input with_union_t s);
  import "DPI-C" function void i_event(input event_t s);

  initial begin
    queue_t q;
    with_union_t u;
    event_t e;
    i_queue(q);
    i_union(u);
    i_event(e);
  end
endmodule
