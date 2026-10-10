// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`begin_keywords "1800+VAMS"

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Unpacked arrays and structs marked with split_var, mostly ones that cannot be split

typedef struct {
  logic [6:0] a;
  logic [4:0] c [1:0];
} st_t;

module t (
    input clk,
    // Primary input, not split
    input logic [6:0] in_arr [2]  /*verilator split_var*/
);

  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;

  // Marked and split, elements of marked aggregates are split too
  st_t st  /*verilator split_var*/;
  // Real and wreal elements, connected to ports
  real vin [0:1]  /*verilator split_var*/;
  wreal vout [0:1]  /*verilator split_var*/;
  // Variable index, not split
  logic [6:0] dyn [4]  /*verilator split_var*/;
  // Referenced whole, not split
  logic [6:0] whole [2]  /*verilator split_var*/;
  // Public, not split
  logic [6:0] pub [2]  /*verilator public*/  /*verilator split_var*/;
  // Not a signal, not split
  localparam logic [6:0] LP [2]  /*verilator split_var*/ = '{7'd1, 7'd2};
  // Forceable, not split
  logic [6:0] fv [2]  /*verilator forceable*/  /*verilator split_var*/;
  // Read or written by DPI exports, not split
  logic [6:0] drd [2]  /*verilator split_var*/;
  logic [6:0] dwr [2]  /*verilator split_var*/;
  // Net delay, not split
  wire [6:0] #1 nd [2]  /*verilator split_var*/;
  // Assignment with a timing control, not split
  logic [6:0] tcd [2]  /*verilator split_var*/;
  // Assigned from 'whole', and also referenced whole, not split
  logic [6:0] whole2 [2]  /*verilator split_var*/;
  // Element referenced whole, the element is not split
  logic [6:0] md2 [2][2]  /*verilator split_var*/;
  typedef logic [6:0] pair_t [2];
  // Referenced whole after member selects, not split
  st_t stw  /*verilator split_var*/;
  pair_t q [$];
  // Connected to the ref task argument and module port
  logic [6:0] rtgt [2];

  always_comb begin
    st.a = crc[6:0];
    st.c[0] = crc[11:7];
    st.c[1] = crc[16:12];
  end

  always_comb begin
    vin[0] = real'(crc[7:0]);
    vin[1] = real'(crc[15:8]);
  end

  rsub u_rsub (.ra(rtgt));

  swap u_swap (
      .in0(vin[0]),
      .in1(vin[1]),
      .out0(vout[0]),
      .out1(vout[1])
  );

  always_comb begin
    for (int i = 0; i < 4; i++) dyn[i] = crc[i*7+:7] ^ in_arr[0];
    whole[0] = crc[6:0];
    whole[1] = crc[13:7];
    pub[0] = ~crc[6:0];
    pub[1] = ~crc[13:7];
  end

  always_comb begin
    fv[0] = crc[6:0];
    fv[1] = crc[13:7];
    drd[0] = crc[6:0];
    drd[1] = crc[13:7];
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 2; j++) md2[i][j] = crc[i*14+j*7+:7];
    end
  end

  export "DPI-C" function dpi_read;
  function int dpi_read();
    return int'(drd[0]);
  endfunction
  export "DPI-C" function dpi_write;
  function void dpi_write(int v);
    dwr[0] = 7'(v);
  endfunction

  assign nd[0] = crc[6:0];
  assign nd[1] = crc[13:7];

  initial tcd = #1 whole;

  always_comb whole2 = whole;

  always_comb begin
    stw.a = crc[6:0];
    stw.c[0] = crc[11:7];
    stw.c[1] = crc[16:12];
  end

  task automatic tsk(input logic [6:0] ia [2]  /*verilator split_var*/,
                     ref logic [6:0] ra [2]  /*verilator split_var*/);
    /*verilator no_inline_task*/
    ra[0] = ia[1];
  endtask

  always @(posedge clk) tsk('{crc[6:0], crc[13:7]}, rtgt);

  always @(posedge clk) begin
    `checkh(LP[0], 7'd1);
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    `checkh(st.a, crc[6:0]);
    `checkh(st.c[0], crc[11:7]);
    `checkh(st.c[1], crc[16:12]);
    `checkh(vout[0] == real'(crc[15:8]), 1'b1);
    `checkh(vout[1] == real'(crc[7:0]), 1'b1);
    `checkh(dyn[crc[1:0]], crc[crc[1:0]*7+:7] ^ in_arr[0]);
    `checkh(whole[0] ^ pub[0], 7'h7f);
    `checkh(whole[1] ^ pub[1], 7'h7f);
    if (cyc == 99) begin
      q.push_back(md2[0]);
      q.insert(1, md2[1]);
      $display("%p %p %p %p %p", whole, whole2, q, md2[0], stw);
      $display("%p", LP);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

// Ref port of a module that is not inlined, not split
module rsub (
    ref logic [6:0] ra [2]  /*verilator split_var*/
);
  /*verilator no_inline_module*/
  initial ra[1] = 7'd1;
endmodule

module swap (
    input wreal in0,
    in1,
    output wreal out0,
    out1
);
  wreal tmp [0:1]  /*verilator split_var*/;
  assign tmp[0] = in0;
  assign tmp[1] = in1;
  assign out0 = tmp[1];
  assign out1 = tmp[0];
endmodule

`end_keywords
