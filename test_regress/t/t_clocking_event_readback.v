// DESCRIPTION: Verilator: APB clocking readback regression
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`timescale 1ns/1ns
// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface apb_if(input bit pclk);
   wire [31:0] paddr;
   wire        psel;
   wire        penable;
   wire        pwrite;
   wire [31:0] prdata;
   wire [31:0] pwdata;

   clocking mck @(posedge pclk);
      output paddr, psel, penable, pwrite, pwdata;
      input  prdata;
   endclocking

   clocking pck @(posedge pclk);
      input paddr, psel, penable, pwrite, prdata, pwdata;
   endclocking
endinterface

module blk(apb_if apb, input bit rst);
   logic [31:0] mode;
   logic [31:0] rate;
   logic [31:0] pr_data;

   assign apb.prdata = (apb.psel && apb.penable) ? pr_data : 'z;

   always_comb begin
      pr_data = 32'h0;
      case (apb.paddr[7:0])
        8'h00: pr_data = mode;
        8'h04: pr_data = rate;
        default: ;
      endcase
   end

   always_ff @(posedge apb.pclk) begin
      if (rst) begin
         mode <= 0;
         rate <= 0;
      end else if (apb.psel && apb.penable && apb.pwrite) begin
         case (apb.paddr[7:0])
           8'h00: mode <= apb.pwdata;
           8'h04: rate <= apb.pwdata;
           default: ;
         endcase
      end
   end
endmodule

module soc(apb_if apb, input bit rst);
   apb_if apb0(apb.pclk);
   apb_if apb1(apb.pclk);
   apb_if apb2(apb.pclk);

   blk blk0(apb0, rst);
   blk blk1(apb1, rst);
   blk blk2(apb2, rst);

   assign apb0.paddr = apb.paddr;
   assign apb0.psel = ((apb.paddr[31:8] == 24'h000000) || (apb.paddr[31:8] == 24'h030000));
   assign apb0.penable = apb.penable;
   assign apb0.pwrite = apb.pwrite;
   assign apb0.pwdata = apb.pwdata;
   assign apb.prdata = apb0.prdata;

   assign apb1.paddr = apb.paddr;
   assign apb1.psel = ((apb.paddr[31:8] == 24'h010000) || (apb.paddr[31:8] == 24'h030000));
   assign apb1.penable = apb.penable;
   assign apb1.pwrite = apb.pwrite;
   assign apb1.pwdata = apb.pwdata;
   assign apb.prdata = apb1.prdata;

   assign apb2.paddr = apb.paddr;
   assign apb2.psel = ((apb.paddr[31:8] == 24'h020000) || (apb.paddr[31:8] == 24'h030000));
   assign apb2.penable = apb.penable;
   assign apb2.pwrite = apb.pwrite;
   assign apb2.pwdata = apb.pwdata;
   assign apb.prdata = apb2.prdata;
endmodule

class Master;
   virtual apb_if vif;

   function new(virtual apb_if vif);
      this.vif = vif;
   endfunction

   task read(input logic [31:0] addr, output logic [31:0] data_mck);
      vif.mck.paddr <= addr;
      vif.mck.pwrite <= 1'b0;
      vif.mck.psel <= 1'b1;
      @(vif.mck);
      vif.mck.penable <= 1'b1;
      @(vif.mck);
      data_mck = vif.mck.prdata;
      $display("READ_SAMPLE t=%0t addr=%08x mck=%08x", $time, addr, data_mck);
      vif.mck.psel <= 1'b0;
      vif.mck.penable <= 1'b0;
   endtask

   task write(input logic [31:0] addr, input logic [31:0] data);
      vif.mck.paddr <= addr;
      vif.mck.pwdata <= data;
      vif.mck.pwrite <= 1'b1;
      vif.mck.psel <= 1'b1;
      @(vif.mck);
      vif.mck.penable <= 1'b1;
      @(vif.mck);
      $display("WRITE_SAMPLE t=%0t addr=%08x data=%08x", $time, addr, data);
      vif.mck.psel <= 1'b0;
      vif.mck.penable <= 1'b0;
   endtask
endclass

module t;
   bit clk = 0;
   bit rst = 1;
   apb_if apb(clk);
   soc dut(apb, rst);

   Master m;

   always #10 clk = ~clk;

   initial begin
      logic [31:0] d0, d1, d2;
      logic [31:0] m0, m1, m2;
      m = new(apb);

      repeat (2) @(posedge clk);
      rst = 0;

      // First phase: direct mode initialization then three reads.
      // This catches first-read timing regressions.
      dut.blk0.mode = 32'h5;
      dut.blk1.mode = 32'h5;
      dut.blk2.mode = 32'h5;
      @(posedge clk);
      m.read(32'h0000_0000, d0);
      m.read(32'h0100_0000, d1);
      m.read(32'h0200_0000, d2);
      $display("FIRST_RESULT d0=%08x d1=%08x d2=%08x", d0, d1, d2);
      `checkd(d0, 32'h0000_0005);
      `checkd(d1, 32'h0000_0005);
      `checkd(d2, 32'h0000_0005);

      // Second phase: broadcast write through the clocking path and readback.
      // This catches mck.prdata sampling regressions.
      m.write(32'h0300_0000, 32'h5);
      m.read(32'h0000_0000, m0);
      m.read(32'h0100_0000, m1);
      m.read(32'h0200_0000, m2);
      $display("SECOND_RESULT m0=%08x m1=%08x m2=%08x", m0, m1, m2);
      `checkd(m0, 32'h0000_0005);
      `checkd(m1, 32'h0000_0005);
      `checkd(m2, 32'h0000_0005);

      $write("*-* All Finished *-*\n");
      $finish;
   end

   always @(apb.pck) begin
      if (apb.pck.psel && apb.pck.penable && !apb.pck.pwrite) begin
         $display("MON_READ t=%0t addr=%08x data=%08x", $time, apb.pck.paddr, apb.pck.prdata);
      end
   end
endmodule
