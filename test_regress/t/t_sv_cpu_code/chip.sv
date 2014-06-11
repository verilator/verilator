// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

// Contributed by M W Lund, Atmel Corporation.

// *****************************************************************************
// Top level of System Verilog evalution (Full chip level)
// *****************************************************************************

module chip
 #( parameter
    NUMPADS = $size( pinout )
  )
 (
  // **** Pinout ****
`ifdef VERILATOR  // see t_tri_array
  inout wire [NUMPADS:1] pad,
`else
  inout wire pad [1:NUMPADS],
`endif

  // **** Inputs !!!! ****
  input  logic clk,
  input  logic rst
  );

  // ***************************************************************************
  // Local Parameters
  // ***************************************************************************

  localparam
            NSLAVES = 2;



  // ***************************************************************************
  // PADS
  // ***************************************************************************

  // **** Interface ****
  pads_if
    padsif();


  // **** Pad Instansiations ****
  pads
//    #( )
      i_pads
        (
         /*AUTOINST*/
         // Interfaces
         .padsif                        (padsif.mp_pads),
         // Inouts
         .pad                           (pad),
         // Inputs
         .clk                           (clk),
         .rst                           (rst));



  // ***************************************************************************
  // "dbus" Interface
  // ***************************************************************************

  genbus_if
    #( .NSLAVES(NSLAVES) )
      dbus( .clk(clk), .rst(rst), .test_mode(1'b0) );

  adrdec
//    #( )
      i_adrdec
        (
         /*AUTOINST*/
         // Interfaces
         .dbus                          (dbus.adrdec));



  // ***************************************************************************
  // CPU ("dbus" Master)
  // ***************************************************************************

  cpu
    #( .ID(1) )
      i_cpu
        (
         /*AUTOINST*/
         // Interfaces
         .dbus                          (dbus.master),
         // Inputs
         .clk                           (clk),
         .rst                           (rst));



  // ***************************************************************************
  // PORTS ("dbus" Slave #1)
  // ***************************************************************************

  ports
    #( .ID(1) )
      i_ports
        (
         /*AUTOINST*/
         // Interfaces
         .dbus                          (dbus.slave),
         .padsif                        (padsif.mp_dig),
         // Inputs
         .clk                           (clk),
         .rst                           (rst));



  // ***************************************************************************
  // Analog Comparator ("dbus" Slave #2)
  // ***************************************************************************

  ac
    #( .ID(2) )
      i_ac
        (
         /*AUTOINST*/
         // Interfaces
         .dbus                          (dbus.slave),
         .padsif                        (padsif.mp_ana),
         // Inputs
         .clk                           (clk),
         .rst                           (rst));



endmodule // chip
