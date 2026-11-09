// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef enum {
  UVM_TLM_READ_COMMAND,
  UVM_TLM_WRITE_COMMAND,
  UVM_TLM_IGNORE_COMMAND
} uvm_tlm_command_e;

module t;

  typedef byte bytes_t[$];
  typedef struct {
    byte hi;
    byte lo;
  } halves_t;
  typedef byte quad_t[4];

  int ones = 0;

  function automatic int one();
    ones++;
    return 1;
  endfunction

  initial begin
    automatic bit array[] = new[8];
    automatic int unsigned m_length;
    automatic uvm_tlm_command_e m_command;

    m_length = 2;
    array = '{0, 0, 0, 0, 0, 0, 1, 0};
    array = new[$bits(m_length)] (array);
    m_command = uvm_tlm_command_e'({<<bit{array}});

    `checkh(m_command, 'h40)

    repeat (16) begin
      // A stream of a fixed-size unpacked array streams the bits of the array
      automatic logic [31:0] v = $urandom;
      automatic logic [31:0] swapped = {v[7:0], v[15:8], v[23:16], v[31:24]};
      byte asc[4];
      byte desc[3:0];
      bytes_t q;
      logic [31:0] w;
      byte nested[2][4];
      {asc[0], asc[1], asc[2], asc[3]} = v;
      {desc[3], desc[2], desc[1], desc[0]} = v;
      `checkh(int'({>>{asc}}), v);
      `checkh(int'({<<8{asc}}), swapped);
      `checkh(int'({>>{desc}}), v);
      `checkh(int'({<<8{desc}}), swapped);
      q = bytes_t'({<<8{asc}});
      `checkh({q[0], q[1], q[2], q[3]}, swapped);
      q = bytes_t'({>>{desc}});
      `checkh({q[0], q[1], q[2], q[3]}, v);
      // Also for a packed value
      q = bytes_t'({>>{v}});
      `checkh({q[0], q[1], q[2], q[3]}, v);
      // Also in another stream, as a source or a target
      `checkh(int'({<<8{{>>{asc}}}}), swapped);
      `checkh(int'({>>{{<<8{desc}}}}), swapped);
      w = {<<8{{>>{asc}}}};
      `checkh(w, swapped);
      {>>{{<<8{asc}}}} = v;
      `checkh({asc[3], asc[2], asc[1], asc[0]}, v);
      // The target of an impure index is selected for each element
      // verilator lint_off SIDEEFFECT
      {>>{{<<8{nested[one()]}}}} = v;
      // verilator lint_on SIDEEFFECT
      `checkh({nested[1][3], nested[1][2], nested[1][1], nested[1][0]}, v);
    end

    repeat (16) begin
      // A stream of a concatenation with a fixed-size unpacked value streams the bits of each
      typedef struct {
        halves_t first;
        halves_t second;
      } pair_t;
      automatic logic [95:0] v = {$urandom, $urandom, $urandom};
      halves_t h;
      byte duo[2];
      halves_t hs[2];  // Of unpacked structs, and declared without a type name
      quad_t quad;
      pair_t pair;
      bytes_t q;
      logic [63:0] w;
      {h.hi, h.lo, duo[0], duo[1], hs[0].hi, hs[0].lo, hs[1].hi, hs[1].lo} = v[95:32];
      {quad[0], quad[1], quad[2], quad[3]} = v[31:0];
      pair = pair_t'({<<8{h, hs[0]}});
      `checkh({pair.first.hi, pair.first.lo}, {v[55:48], v[63:56]});
      `checkh({pair.second.hi, pair.second.lo}, {v[87:80], v[95:88]});
      `checkh(int'({>>{h, hs[0]}}), {v[95:80], v[63:48]});
      `checkh(longint'({>>{hs, quad}}), v[63:0]);
      q = bytes_t'({>>{duo, h}});
      `checkh({q[0], q[1], q[2], q[3]}, {v[79:64], v[95:80]});
      // An impure value split between members is evaluated once
      ones = 0;
      pair = pair_t'({>>{h, 16'(one())}});
      `checkh({pair.first.hi, pair.first.lo, pair.second.hi, pair.second.lo}, {v[95:80], 16'h1});
      `checkh(ones, 1);
      // Also assigned, as a source or a target
      w = {>>{hs, quad}};
      `checkh(w, v[63:0]);
      {<<8{h, quad}} = v[47:0];
      `checkh({h.hi, h.lo}, {v[7:0], v[15:8]});
      `checkh({quad[0], quad[1], quad[2], quad[3]}, {v[23:16], v[31:24], v[39:32], v[47:40]});
      // Also nonblocking, in a process with timing controls
      {<<8{h, duo}} <= v[31:0];
      #1;
      `checkh({h.hi, h.lo}, {v[7:0], v[15:8]});
      `checkh({duo[0], duo[1]}, {v[23:16], v[31:24]});
    end

    repeat (16) begin
      // A cast to an unpacked array is converted whole, e.g. streamed
      typedef logic [47:0] bits48_t;
      typedef logic [39:0] fives_t[2];
      automatic logic [31:0] v = $urandom;
      automatic logic [31:0] swapped = {v[7:0], v[15:8], v[23:16], v[31:24]};
      logic [47:0] m;
      logic [31:0] w;
      logic [79:0] wide;
      byte dyn[];
      bytes_t q;
      m = bits48_t'({<<16{16'h0102, quad_t'(v)}});
      `checkh(m, {v[15:0], v[31:16], 16'h0102});
      m = {<<16{16'h0102, quad_t'(v)}};
      `checkh(m, {v[15:0], v[31:16], 16'h0102});
      w = {<<8{quad_t'(v)}};
      `checkh(w, swapped);
      wide = {v, 48'h0708090a0b0c};
      wide = {<<40{fives_t'(wide)}};
      `checkh(wide, {40'h08090a0b0c, v, 8'h07});
      q = {<<8{quad_t'(v)}};
      `checkh({q[0], q[1], q[2], q[3]}, swapped);
      dyn = quad_t'(v);
      `checkh({dyn[0], dyn[1], dyn[2], dyn[3]}, v);
      // A cast in the slice size of an assignment target is only read
      {<<$bits(halves_t'(v[15:0])) {w}} = 32'h11223344;
      `checkh(w, 32'h33441122);
    end

    repeat (16) begin
      // A cast of a stream is as if assigned, so to a wider type it fills zeros on the right
      // (IEEE 1800-2023 6.24.1, 11.4.14)
      automatic logic [30:0] v = 31'($urandom);
      `checkh(longint'({<<16{v}}), {v[15:0], v[30:16], 33'h0});
      // Also as a system function argument, of the size of the cast
      `checks($sformatf("%h", 33'({<<16{v}})), $sformatf("%h", {v[15:0], v[30:16], 2'b0}));
      // A size cast of the same size, also as a system task argument
      `checkh(31'({<<16{v}}), {v[15:0], v[30:16]});
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
