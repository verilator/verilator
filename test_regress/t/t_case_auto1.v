// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   localparam // synopsys enum En_State
              EP_State_IDLE =           {3'b000,5'd00},
              EP_State_CMDSHIFT0 =      {3'b001,5'd00},
              EP_State_CMDSHIFT13 =     {3'b001,5'd13},
              EP_State_CMDSHIFT14 =     {3'b001,5'd14},
              EP_State_CMDSHIFT15 =     {3'b001,5'd15},
              EP_State_CMDSHIFT16 =     {3'b001,5'd16},
              EP_State_DWAIT =          {3'b010,5'd00},
              EP_State_DSHIFT0 =        {3'b100,5'd00},
              EP_State_DSHIFT1 =        {3'b100,5'd01},
              EP_State_DSHIFT15 =       {3'b100,5'd15};

   reg [7:0]    /* synopsys enum En_State */
                m_state_xr;             // Last command, for debugging
   /*AUTOASCIIENUM("m_state_xr", "m_stateAscii_xr", "EP_State_")*/
   // Beginning of automatic ASCII enum decoding
   reg [79:0]           m_stateAscii_xr;        // Decode of m_state_xr
   always @(m_state_xr) begin
      case ({m_state_xr})
        EP_State_IDLE:       m_stateAscii_xr = "idle      ";
        EP_State_CMDSHIFT0:  m_stateAscii_xr = "cmdshift0 ";
        EP_State_CMDSHIFT13: m_stateAscii_xr = "cmdshift13";
        EP_State_CMDSHIFT14: m_stateAscii_xr = "cmdshift14";
        EP_State_CMDSHIFT15: m_stateAscii_xr = "cmdshift15";
        EP_State_CMDSHIFT16: m_stateAscii_xr = "cmdshift16";
        EP_State_DWAIT:      m_stateAscii_xr = "dwait     ";
        EP_State_DSHIFT0:    m_stateAscii_xr = "dshift0   ";
        EP_State_DSHIFT1:    m_stateAscii_xr = "dshift1   ";
        EP_State_DSHIFT15:   m_stateAscii_xr = "dshift15  ";
        default:             m_stateAscii_xr = "%Error    ";
      endcase
   end
   // End of automatics

   integer    cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         //$write("%d %x %x %x\n", cyc, data, wrapcheck_a, wrapcheck_b);
         if (cyc==1) begin
            m_state_xr <= EP_State_IDLE;
         end
         if (cyc==2) begin
            if (m_stateAscii_xr != "idle      ") $stop;
            m_state_xr <= EP_State_CMDSHIFT13;
         end
         if (cyc==3) begin
            if (m_stateAscii_xr != "cmdshift13") $stop;
            m_state_xr <= EP_State_CMDSHIFT16;
         end
         if (cyc==4) begin
            if (m_stateAscii_xr != "cmdshift16") $stop;
            m_state_xr <= EP_State_DWAIT;
         end
         if (cyc==9) begin
            if (m_stateAscii_xr != "dwait     ") $stop;
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule
