// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
// Call the C++-linkage wrapper of a test function, as $c cannot declare an extern "C" function
`define CPP_CALL(f) $c32(`"[] { extern int f``_cpp(); return f``_cpp(); }()`")
// verilog_format: on

module t;


  typedef enum logic [1:0] {
    E_A,
    E_B,
    E_C,
    E_D
  } e_t;

  // 12 bits
  typedef struct packed {
    logic [3:0] hi;  // [11:8]
    e_t e;  // [7:6]
    logic signed [5:0] lo;  // [5:0]
  } s_t;

  // 12 bits
  typedef union packed {
    logic [11:0] raw;
    s_t s;
  } u_t;

  // 24 bits
  typedef struct packed {
    logic [3:0] tag;  // [23:20]
    s_t inner;  // [19:8]
    logic [3:0][1:0] pa;  // [7:0]
  } n_t;

  // 100 bits, VlWide<4>
  typedef struct packed {
    logic [11:0] top;  // [99:88]
    logic [39:0] wide;  // [87:48], spans three 32-bit words
    logic [19:0] mid;  // [47:28], straddles bit 32
    logic [7:0] b8;  // [27:20]
    logic [19:0] low;  // [19:0]
  } w_t;

  // 28 bits
  typedef struct packed {
    logic [2:0] a;  // [27:25]
    s_t [1:0] sub;  // [24:1], sub[1] is [24:13], sub[0] is [12:1]
    logic b;  // [0]
  } m_t;

  // Unpacked struct with a packed struct member
  typedef struct {
    s_t p;
    logic [6:0] x;
  } us_t;

  s_t s  /*verilator public_flat_rw*/;
  u_t u  /*verilator public_flat_rw*/;
  n_t n  /*verilator public_flat_rw*/;
  w_t w  /*verilator public_flat_rw*/;
  m_t m  /*verilator public_flat_rw*/;
  s_t [3:0] arr  /*verilator public_flat_rw*/;
  s_t uarr[2]  /*verilator public_flat_rw*/;
  s_t [1:0][2:0] arr2  /*verilator public_flat_rw*/;
  n_t [1:0] narr  /*verilator public_flat_rw*/;
  s_t fs  /*verilator public_flat_rw*/  /*verilator forceable*/;
  logic [3:0][1:0] pvec  /*verilator public_flat_rw*/;
  us_t us  /*verilator public_flat_rw*/;
  localparam s_t PS  /*verilator public_flat_rd*/ = '{hi: 4'h3, e: E_C, lo: -6'sd5};
  localparam n_t PN  /*verilator public_flat_rd*/ = '{
      tag: 4'h5,
      inner: '{hi: 4'h7, e: E_D, lo: 6'sd3},
      pa: 8'hc6
  };
  localparam w_t PW[2]  /*verilator public_flat_rd*/ = '{
      '{top: 12'h0, wide: 40'h0, mid: 20'h0, b8: 8'h11, low: 20'h0},
      '{top: 12'habc, wide: 40'h0, mid: 20'h0, b8: 8'h5a, low: 20'h12345}
  };
  localparam s_t [1:0] P4D[2][2]  /*verilator public_flat_rd*/ = '{
      '{24'h111222, 24'h333444},
      '{24'h9c0555, 24'h666777}
  };
  w_t uw[2]  /*verilator public_flat_rw*/;
  wire s_t sn  /*verilator public_flat_rd*/;
  wire u_t un  /*verilator public_flat_rd*/;

  assign sn = s;
  assign un = u;

  logic clk;
  int cyc;
  int status;

  initial clk = 0;
  always #5 clk = ~clk;

  initial begin
    s = '0;
    u = '0;
    n = '0;
    w = '0;
    m = '0;
    arr = '0;
    uarr[0] = '0;
    uarr[1] = '0;
    uw[0] = '0;
    uw[1] = '0;
    arr2 = '0;
    narr = '0;
    fs = '0;
    pvec = '0;
    us = '{default: '0};
    cyc = 0;
    // Static checks, then register the value change callbacks
`ifdef VERILATOR
    status = `CPP_CALL(mon_check);
`else
    status = $mon_check;
`endif
    if (status != 0) begin
      $write("%%Error: t_vpi_packed_struct.cpp: mon_check failed\n");
      `stop;
    end
  end

  // Change watched members and their siblings at known cycles, see t_vpi_packed_struct.cpp
  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      2: s.hi <= 4'h9;
      3: s.lo <= 6'sd7;
      4: s.e <= E_A;
      5: w.wide <= '0;
      6: w.top <= '0;
      7: w.mid <= 20'h1;
      8: arr[1].e <= E_D;
      9: arr[2].hi <= 4'h1;
      10: arr[2].e <= E_B;
      11: pvec[0] <= 2'd3;
      12: pvec[3] <= 2'd2;
      13: begin
`ifdef VERILATOR
        status = `CPP_CALL(mon_check_cbs);
`else
        status = $mon_check_cbs;
`endif
        if (status != 0) begin
          $write("%%Error: t_vpi_packed_struct.cpp: mon_check_cbs failed\n");
          `stop;
        end
        $write("*-* All Finished *-*\n");
        $finish;
      end
      default: ;
    endcase
  end

endmodule
