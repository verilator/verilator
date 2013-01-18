// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

`define RegDel	1

module t_mem_slot (Clk, SlotIdx, BitToChange, BitVal, SlotToReturn, OutputVal);

   input        Clk;
   input  [1:0] SlotIdx;
   input        BitToChange;
   input        BitVal;
   input  [1:0] SlotToReturn;
   output [1:0] OutputVal;

   reg    [1:0] Array[2:0];

   always @(posedge Clk)
   begin
      Array[SlotIdx][BitToChange] <= #`RegDel BitVal;

      OutputVal = Array[SlotToReturn];
   end
endmodule
