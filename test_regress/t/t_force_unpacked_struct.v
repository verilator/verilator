// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;

  typedef struct {
    int   x;
    logic y;
  } struct_t;

  struct_t s_array[3];
  struct_t my_struct;

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      s_array[1].x = 1;
      my_struct.x <= 1;
    end
    else if (cyc == 1) begin
      `checkh(s_array[1].x, 1);
      `checkh(my_struct.x, 1);
    end
    else if (cyc == 2) begin
      force s_array[1].x = 0;
      force my_struct.x = 0;
    end
    else if (cyc == 3) begin
      `checkh(s_array[1].x, 0);
      s_array[1].x = 1;
      `checkh(my_struct.x, 0);
      my_struct.x <= 1;
    end
    else if (cyc == 4) begin
      `checkh(s_array[1].x, 0);
      `checkh(my_struct.x, 0);
    end
    else if (cyc == 5) begin
      release s_array[1].x;
      release my_struct.x;
    end
    else if (cyc == 6) begin
      `checkh(s_array[1].x, 0);
      s_array[1].x = 1;
      `checkh(my_struct.x, 0);
      my_struct.x <= 1;
    end
    else if (cyc == 7) begin
      `checkh(s_array[1].x, 1);
      `checkh(my_struct.x, 1);
    end
    else if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
