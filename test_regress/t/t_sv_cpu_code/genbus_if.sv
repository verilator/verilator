// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

// Contributed by M W Lund, Atmel Corporation.

typedef struct packed
               {
                 bit [1:0] size;
               } mPreAdrDecode_resp;


interface genbus_if
 #( parameter
      DSIZE    = 2,
      SSIZE    = DSIZE,
      ASIZE    = 16,
      NMASTERS = 1,
      NSLAVES  = 1,
      DMSB     = (DSIZE<<3) - 1,
      SMSB     = SSIZE - 1,
      AMSB     = ASIZE - 1
  )
 (
  // **** Inputs ****

  // - System -
  input  logic        clk,              // Device Clock.
  input  logic        rst,              // Device Reset.
  input  logic        test_mode         // Test mode.
 );

  // ***************************************************************************
  // Interface Variables
  // ***************************************************************************

  // **** Master ****
  logic [DMSB:0] m_sdata[1:NMASTERS];   // Slave data.
  logic          m_ws   [1:NMASTERS];   // Slave wait state.
  logic [DMSB:0] m_mdata[1:NMASTERS];   // Master data.
  logic [AMSB:0] m_adr  [1:NMASTERS];   // Address.
  logic [SMSB:0] m_we   [1:NMASTERS];   // Write enable.
  logic [SMSB:0] m_re   [1:NMASTERS];   // Read enable.


  // **** Slave ****
  logic [DMSB:0] s_sdata[1:NSLAVES];    // Slave data       (from slave).
  logic          s_ws   [1:NSLAVES];    // Slave wait state (from slave).
  logic [DMSB:0] s_mdata[1:NSLAVES];    // Master data      (to slave).
  logic [AMSB:0] s_adr  [1:NSLAVES];    // Address          (to slave).
  logic [SMSB:0] s_we   [1:NSLAVES];    // Write enable     (to slave).
  logic [SMSB:0] s_re   [1:NSLAVES];    // Read enable      (to slave).


  // **** Address Decoder ****
  logic          s_sel  [1:NSLAVES];    // Slave select (to slave).



  // ***************************************************************************
  // Modports
  // ***************************************************************************

  modport master(
                  import mConnect,
                  import mPreAdrDecode,
                  input  m_sdata,
                  input  m_ws,
                  output m_mdata,
                  output m_adr,
                  output m_we,
                  output m_re
                 );

  // - Slaves -
  modport slave(
                 import sConnect,
                 output s_sdata,
                 output s_ws,
                 input  s_mdata,
                 input  s_adr,
                 input  s_we,
                 input  s_re,
                 input  s_sel
                );

// UNSUPPORTED
//  for (genvar i = 1; i <= NSLAVES; i++ )
//    begin: mps
//      modport slave(
//                    import sConnect,
//                    output .s_sdata( s_sdata[i] ),
//                    output .s_ws   ( s_ws   [i] ),
//                    input  .s_mdata( s_mdata[i] ),
//                    input  .s_adr  ( s_adr  [i] ),
//                    input  .s_we   ( s_we   [i] ),
//                    input  .s_re   ( s_re   [i] ),
//                    input  .s_sel  ( s_sel  [i] )
//                    );
//    end

//   blocks

  modport adrdec(
                  import aNumSlaves,
                  input  s_adr,
                  output s_sel
                 );



  // ***************************************************************************
  // Bus Multiplexers
  // ***************************************************************************

  always_comb
    begin: busmux
      // - Local Variables -
      integer i;

      // - Defautls -
      m_sdata[1] = {(DSIZE<<3){1'b0}};
      m_ws   [1] = 1'b0;

      for ( i = 1; i <= NSLAVES; i++ )
        begin
          m_sdata[1] |= s_sdata[i];
          m_ws   [1] |= s_ws   [i];

          s_mdata[i]  = m_mdata[1];
          s_adr  [i]  = m_adr  [1];
          s_we   [i]  = m_we   [1];
          s_re   [i]  = m_re   [1];
        end
    end



  // ***************************************************************************
  // Master Functions and Tasks
  // ***************************************************************************

  function automatic void mConnect( input  integer          id,
                                    output logic   [DMSB:0] sdata,
                                    output logic            ws,
                                    input  logic   [DMSB:0] mdata,
                                    input  logic   [AMSB:0] adr,
                                    input  logic   [SMSB:0] we,
                                    input  logic   [SMSB:0] re  );
    begin
      m_mdata[id] = mdata;
      m_adr  [id] = adr;
      m_we   [id] = we;
      m_re   [id] = re;

      sdata = m_sdata[id];
      ws    = m_ws   [id];
    end
  endfunction


  function automatic mPreAdrDecode_resp mPreAdrDecode( input  integer          id,
                                                       input  logic   [AMSB:0] adr );
    begin
      // ToDo: Add parameterized address decoding!!!!

      // Example code:
      if ( adr[0] )
        mPreAdrDecode.size = 2'b01;   // Word (16-bit) memory.
      else
        mPreAdrDecode.size = 2'b10;   // Double Word (32-bit) memory.
    end
  endfunction



  // ***************************************************************************
  // Slave Functions and Tasks
  // ***************************************************************************

  function automatic void sConnect( input  integer          id,
                                    input  logic            rst,
                                    input  logic   [DMSB:0] sdata,
                                    input  logic            ws,
                                    output logic   [DMSB:0] mdata,
                                    output logic   [AMSB:0] adr,
                                    output logic   [SMSB:0] we,
                                    output logic   [SMSB:0] re );
    begin
      s_sdata[id] = sdata & {(DSIZE<<3){s_sel[id]}};
      // verilator lint_off WIDTH
      s_ws   [id] = ws & {SSIZE{s_sel[id]}};
      // verilator lint_on WIDTH

      mdata  = s_mdata[id] & {16{~rst}};
      adr    = s_adr  [id];
      we     = (s_we   [id] & {SSIZE{s_sel[id]}}) | {SSIZE{rst}};
      re     = s_re   [id] & {SSIZE{s_sel[id]}};
    end
  endfunction



  // ***************************************************************************
  // Address Decoder Functions and Tasks
  // ***************************************************************************


  function automatic integer aNumSlaves;
     aNumSlaves = NSLAVES;
  endfunction

endinterface // genbus_if
