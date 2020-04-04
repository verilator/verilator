// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   enum integer {

	      EP_State_IDLE  		,
	      EP_State_CMDSHIFT0  	,
	      EP_State_CMDSHIFT13  	,
	      EP_State_CMDSHIFT14  	,
	      EP_State_CMDSHIFT15  	,
	      EP_State_CMDSHIFT16  	,
	      EP_State_DWAIT  		,
	      EP_State_DSHIFT0  	,
	      EP_State_DSHIFT1  	,
	      EP_State_DSHIFT15  	} m_state_xr, m_state2_xr;

   // Beginning of automatic ASCII enum decoding
   reg [79:0]		m_stateAscii_xr;	// Decode of m_state_xr
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
	    m_state2_xr <= EP_State_IDLE;
	 end
	 if (cyc==2) begin
	    if (m_stateAscii_xr != "idle      ") $stop;
	    m_state_xr <= EP_State_CMDSHIFT13;
	    if (m_state2_xr != EP_State_IDLE) $stop;
	    m_state2_xr <= EP_State_CMDSHIFT13;
	 end
	 if (cyc==3) begin
	    if (m_stateAscii_xr != "cmdshift13") $stop;
	    m_state_xr <= EP_State_CMDSHIFT16;
	    if (m_state2_xr != EP_State_CMDSHIFT13) $stop;
	    m_state2_xr <= EP_State_CMDSHIFT16;
	 end
	 if (cyc==4) begin
	    if (m_stateAscii_xr != "cmdshift16") $stop;
	    m_state_xr <= EP_State_DWAIT;
	    if (m_state2_xr != EP_State_CMDSHIFT16) $stop;
	    m_state2_xr <= EP_State_DWAIT;
	 end
	 if (cyc==9) begin
	    if (m_stateAscii_xr != "dwait     ") $stop;
	    if (m_state2_xr != EP_State_DWAIT) $stop;
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule
