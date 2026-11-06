// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Bit-stream casts to and from unpacked structs (IEEE 1800-2023 6.24.3)

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Monitor;
  typedef struct {
    logic [63:56] dev;
    logic [55:48] cmd;
    logic [47:0] val;
  } tohost_t;

  function longint get_val(longint v);
    return v;
  endfunction

  function string check_tohost(longint v);
    tohost_t tohost_value;
    tohost_value = tohost_t'(get_val(v));
    if (tohost_value.dev !== v[63:56] || tohost_value.cmd !== v[55:48]
        || tohost_value.val !== v[47:0] || longint'(tohost_value) != v)
      return $sformatf(
          "dev=%h cmd=%h val=%h back=%h",
          tohost_value.dev,
          tohost_value.cmd,
          tohost_value.val,
          longint'(tohost_value)
      );
    return "";
  endfunction
endclass

module t (
    input clk
);

  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;
  logic [63:0] crc_last;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    crc_last <= crc;
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Casts between longint and an unpacked struct, in a class
  Monitor mon = new;
  always @(posedge clk) begin
    `checks(mon.check_tohost(crc), "");
  end

  typedef enum logic [2:0] {
    E0 = 3'd0,
    E5 = 3'd5
  } enum_t;

  typedef struct packed {
    logic [3:0] hi;
    bit [2:0] lo;
  } packed_t;

  typedef struct {
    logic [6:0] a;
    shortint s;
    enum_t e;
    packed_t p;
  } inner_t;

  typedef struct {
    inner_t in;
    byte desc[3:1];
    bit [19:0] w;
    logic [1:0] m[2:1][0:2];
    logic [2:0] asc[1:2];
  } outer_t;

  typedef struct {
    logic [64:0] x;
    bit [29:0] y;
  } other_t;

  typedef logic [94:0] bits95_t;

  // Members and elements are leftmost first, and nested
  always @(posedge clk) begin
    automatic bits95_t v = {crc[30:0], crc};
    automatic outer_t o = outer_t'(v);
    automatic other_t ot = other_t'(o);
    `checkh(o.in.a, v[94:88]);
    `checkh(o.in.s, v[87:72]);
    `checkh(o.in.e, v[71:69]);
    `checkh(o.in.p, v[68:62]);
    `checkh(o.desc[3], v[61:54]);
    `checkh(o.desc[2], v[53:46]);
    `checkh(o.desc[1], v[45:38]);
    `checkh(o.w, v[37:18]);
    `checkh(o.m[2][0], v[17:16]);
    `checkh(o.m[2][1], v[15:14]);
    `checkh(o.m[2][2], v[13:12]);
    `checkh(o.m[1][0], v[11:10]);
    `checkh(o.m[1][1], v[9:8]);
    `checkh(o.m[1][2], v[7:6]);
    `checkh(o.asc[1], v[5:3]);
    `checkh(o.asc[2], v[2:0]);
    `checkh(bits95_t'(o), v);
    // Between structs of different layouts
    `checkh(ot.x, v[94:30]);
    `checkh(ot.y, v[29:0]);
    `checkh(bits95_t'(outer_t'(ot)), v);
    // To the same type
    `checkh(bits95_t'(outer_t'(o)), v);
  end

  function automatic bits95_t roundtrip(bits95_t v);
    return bits95_t'(outer_t'(v));
  endfunction

  // Nested casts in assignments
  always @(posedge clk) begin
    automatic bits95_t v = {crc[30:0], crc};
    automatic bits95_t v2;
    v2 = bits95_t'(outer_t'(v));
    `checkh(v2, v);
    `checkh(roundtrip(v), v);
  end

  // The example of IEEE 1800-2023 6.24.3, between an unpacked struct and an unpacked array
  typedef struct {
    shortint address;
    logic [3:0] code;
    byte command[2];
  } Control;

  typedef bit Bits[36:1];

  typedef logic [35:0] bits36_t;

  always @(posedge clk) begin
    automatic Control p = '{crc[35:20], crc[19:16], '{crc[15:8], crc[7:0]}};
    automatic Control q;
    automatic Bits stream[$];
    automatic Bits b;
    stream.push_back(Bits'(p));
    b = stream[0];
    `checkh(b[36], crc[35]);
    `checkh(b[1], crc[0]);
    `checkh(bits36_t'(b), crc[35:0]);
    q = Control'(b);
    `checkh(q.address, crc[35:20]);
    `checkh(q.code, crc[19:16]);
    `checkh(q.command[0], crc[15:8]);
    `checkh(q.command[1], crc[7:0]);
  end

  typedef byte bytes_t[4];
  typedef byte bytes_desc_t[3:0];
  typedef logic [3:0] nibbles_t[2][4];

  // Casts of unpacked arrays, leftmost element first
  always @(posedge clk) begin
    automatic bytes_t a = bytes_t'(crc[31:0]);
    automatic bytes_desc_t d = bytes_desc_t'(a);
    automatic nibbles_t n = nibbles_t'(a);
    automatic bytes_t same = bytes_t'(a);
    `checkh(a[0], crc[31:24]);
    `checkh(a[3], crc[7:0]);
    `checkh(int'(a), crc[31:0]);
    `checkh(d[3], crc[31:24]);
    `checkh(d[0], crc[7:0]);
    `checkh(n[0][0], crc[31:28]);
    `checkh(n[1][3], crc[3:0]);
    `checkh(int'(n), crc[31:0]);
    `checkh(int'(same), crc[31:0]);
    `checkh(int'(bytes_t'{1: crc[15:8], default: 8'h5a}), {8'h5a, crc[15:8], 16'h5a5a});
    `checkh(d == bytes_desc_t'(a), 1'b1);
    `checkh(int'(bytes_desc_t'(a)), crc[31:0]);
  end

  typedef real reals_t[1:2];
  typedef Monitor monitors_t[3:2];

  // Casts between equivalent arrays, of any elements, are as assigned (IEEE 1800-2023 6.24.1)
  always @(posedge clk) begin
    automatic real r[2] = '{real'(cyc), 0.5};
    automatic reals_t rr = reals_t'(r);
    automatic Monitor m[2] = '{mon, null};
    automatic monitors_t mm = monitors_t'(m);
    `checkh(rr[1] == real'(cyc), 1'b1);
    `checkh(rr[2] == 0.5, 1'b1);
    `checkh(mm[3] == mon, 1'b1);
    `checkh(mm[2] == null, 1'b1);
  end

  typedef struct {
    real r;
    int q[$];
  } dynamic_t;

  // Casts to a matching type, of any members or elements, are as assigned (IEEE 1800-2023 6.24.1)
  always @(posedge clk) begin
    automatic dynamic_t d;
    automatic dynamic_t same;
    automatic reals_t r = '{real'(cyc), 0.5};
    automatic reals_t same_r = reals_t'(r);
    d.r = real'(cyc);
    d.q.push_back(cyc);
    same = dynamic_t'(d);
    `checkh(same.r == real'(cyc), 1'b1);
    `checkd(same.q.size(), 1);
    `checkd(same.q[0], cyc);
    `checkh(same_r[1] == real'(cyc), 1'b1);
    `checkh(same_r[2] == 0.5, 1'b1);
  end

  typedef struct {
    shortint hi;
    logic [15:0] lo;
  } halves_t;

  typedef struct {logic [2:0] f;} field_t;

  typedef struct {
    bit [2:0] f;
    logic [3:0] g;
  } fields_t;

  // Integral targets and members keep their type
  always @(posedge clk) begin
    automatic halves_t h = halves_t'(crc[31:0]);
    `checkd(int'(h.hi), int'($signed(crc[31:16])));
    `checkd(int'(h), $signed(crc[31:0]));
    `checkd(int'(h) < 0, crc[31]);
    `checkh(enum_t'(field_t'(crc[2:0])), crc[2:0]);
    `checkh(packed_t'(fields_t'(crc[6:0])), crc[6:0]);
  end

  int calls = 0;

  function automatic logic [31:0] count_crc();
    calls++;
    return crc[31:0];
  endfunction

  function automatic halves_t count_halves();
    calls++;
    return halves_t'(crc[31:0]);
  endfunction

  function automatic halves_t halves_of_count();
    return halves_t'(count_crc());
  endfunction

  // Impure values are evaluated once
  always @(posedge clk) begin
    automatic halves_t h;
    automatic bytes_t a;
    calls = 0;
    h = halves_t'(count_crc());
    `checkh(h.lo, crc[15:0]);
    a = bytes_t'(count_halves());
    `checkh(int'(a), crc[31:0]);
    a = bytes_t'(halves_t'{shortint'(count_crc() >> 16), crc[15:0]});
    `checkh(int'(a), crc[31:0]);
    `checkh(int'({<<8{count_halves()}}), {crc[7:0], crc[15:8], crc[23:16], crc[31:24]});
    h = halves_of_count();
    `checkh(h.lo, crc[15:0]);
    `checkd(calls, 5);
  end

  int value_calls = 0;

  function automatic logic [31:0] count_value(logic [31:0] v);
    value_calls++;
    return v;
  endfunction

  // verilator lint_off SIDEEFFECT
  function automatic halves_t default_halves(halves_t h = halves_t'(count_value(32'h12345678)));
    return h;
  endfunction

  function halves_t static_halves();
    static halves_t h = halves_t'(count_value(32'h9abcdef0));
    return h;
  endfunction
  // verilator lint_on SIDEEFFECT

  // In a function, but evaluated where called, or before running
  always @(posedge clk) begin
    `checkh(int'(default_halves()), 32'h12345678);
    `checkh(int'(static_halves()), 32'h9abcdef0);
  end

  function int static_user();
    static int s = index_of(32'h1);
    return s;
  endfunction

  // Also in a function first used there, and in the indices of an assignment target
  always @(posedge clk) begin
    automatic int targets[4] = '{default: 0};
    value_calls = 0;
    targets[index_of(32'h2)] = 1;
    targets[int'(halves_t'(count_value(32'h3)))] = 2;
    `checkd(value_calls, 2);
    `checkd(targets[2], 1);
    `checkd(targets[3], 2);
  end

  function automatic int index_of(logic [31:0] v);
    return int'(halves_t'(count_value(v))) & 3;
  endfunction

  // In a property of a class, of each specialization, with temporaries in the module
  class Counted #(
      int N = 0
  );
    halves_t h = halves_t'(count_crc());
  endclass

  always @(posedge clk) begin
    Counted #(1) one;
    Counted #(2) two;
    calls = 0;
    one = new;
    two = new;
    `checkh(int'(one.h), crc[31:0]);
    `checkh(int'(two.h), crc[31:0]);
    `checkd(calls, 2);
  end

  function automatic int one_count();
    value_calls++;
    return 1;
  endfunction

  function automatic logic [31:0] const_element();
    const halves_t consts[2] = '{'{16'h1234, 16'h5678}, '{16'h9abc, 16'hdef0}};
    return int'(consts[one_count()]);
  endfunction

  // An impure value of a const type
  always @(posedge clk) begin
    `checkh(const_element(), 32'h9abcdef0);
  end

  typedef struct {
    logic [8:0] x;
    logic [8:0] y;
  } s18_t;

  // A stream of an unpacked array or struct streams the bits of the value
  always @(posedge clk) begin
    automatic logic [2:0] m[2][3];
    automatic halves_t h = halves_t'(crc[31:0]);
    automatic halves_t swapped = halves_t'({<<16{h}});
    automatic s18_t s18;
    {m[0][0], m[0][1], m[0][2], m[1][0], m[1][1], m[1][2]} = crc[17:0];
    s18 = s18_t'({>>{m}});
    `checkh({s18.x, s18.y}, crc[17:0]);
    s18 = s18_t'({<<3{m}});
    `checkh({s18.x, s18.y}, {m[1][2], m[1][1], m[1][0], m[0][2], m[0][1], m[0][0]});
    // The leftmost block is shorter
    s18 = s18_t'({<<4{m}});
    `checkh({s18.x, s18.y}, {crc[3:0], crc[7:4], crc[11:8], crc[15:12], crc[17:16]});
    // In another stream
    s18 = s18_t'({<<9{{>>{m}}}});
    `checkh({s18.x, s18.y}, {crc[8:0], crc[17:9]});
    `checkh(swapped.hi, crc[15:0]);
    `checkh(swapped.lo, crc[31:16]);
    `checkh(int'({<<16{h}}), {crc[15:0], crc[31:16]});
  end

  typedef struct {
    byte hi;
    logic [6:0] lo;
  } s15_t;

  typedef logic [14:0] bits15_t;

  function automatic s15_t to_s15(bits15_t v);
    return s15_t'(v);
  endfunction

  function automatic bits15_t from_s15(s15_t s);
    return bits15_t'(s);
  endfunction

  // In continuous and nonblocking assignments, function arguments and returns
  s15_t s15_w;
  bits15_t back_w;
  s15_t s15_q;
  assign s15_w = s15_t'(crc[14:0]);
  assign back_w = bits15_t'(s15_w);
  always @(posedge clk) begin
    s15_q <= s15_t'(crc[14:0]);
    `checkh(s15_w.hi, crc[14:7]);
    `checkh(s15_w.lo, crc[6:0]);
    `checkh(back_w, crc[14:0]);
    if (cyc > 0) `checkh(bits15_t'(s15_q), crc_last[14:0]);
    `checkh(from_s15(to_s15(crc[14:0])), crc[14:0]);
    `checkh(from_s15(s15_t'(crc[29:15])), crc[29:15]);
  end

  function automatic halves_t checked_halves(logic [31:0] v);
    if (v == 0) $error("Zero");
    return halves_t'(v);
  endfunction

  function automatic int checked_int(logic [31:0] v);
    return int'(checked_halves(v));
  endfunction

  // In an input port connection
  int pass_out;
  sub_pass u_pass (
      .i(int'(checked_halves({crc[31:1], 1'b1}))),
      .o(pass_out)
  );
  always @(posedge clk) begin
    `checkh(pass_out, {crc[31:1], 1'b1});
  end

  // In constants
  localparam s15_t P = s15_t'(15'h2bcd);
  localparam bits15_t L = bits15_t'(P);
  localparam int C = int'(checked_halves(32'h12345678));
  localparam int D = checked_int(32'h9abcdef0);
  initial begin
    `checkh(P.hi, 8'h57);
    `checkh(P.lo, 7'h4d);
    `checkh(L, 15'h2bcd);
    `checkh(C, 32'h12345678);
    `checkh(D, 32'h9abcdef0);
  end

`ifdef VERILATOR
  // As in an assigned stream, a real member streams as its 64 bits, an extension of the standard
  typedef struct {
    real r;
    logic [6:0] t;
  } real_t;

  typedef logic [70:0] bits71_t;

  always @(posedge clk) begin
    automatic real_t rs = '{real'(cyc) / 4.0, crc[6:0]};
    `checkh(bits71_t'({>>{rs}}), {$realtobits(rs.r), rs.t});
  end
`endif

endmodule

module sub_pass (
    input int i,
    output int o
);
  assign o = i;
endmodule
