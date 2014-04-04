// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

// Contributed by M W Lund, Atmel Corporation.

module ac_dig
 #( parameter
      ID = 1 )
 (
  // ***************************************************************************
  // Module Interface (interfaces, outputs, and inputs)
  // ***************************************************************************

  // **** Interfaces ****
  genbus_if.slave dbus,


  // **** Outputs ****
  output logic       acenable,


  // **** Inputs ****
  input  logic       acout,


  // - System -
  input  logic       clk,
  input  logic       rst
 );

  // ***************************************************************************
  // Regs and Wires
  // ***************************************************************************

  // **** Internal Data Bus ****
  logic [15:0] sdata;
  logic        ws;
  logic [15:0] mdata;
  logic [15:0] adr;
  logic [1:0]  we;
  logic [1:0]  re;


  // **** User Registers ****
  struct packed
  {
    logic [7:1] reserved;
    logic       enable;
  } control;

  struct packed
  {
    logic [7:1] reserved;
    logic       acout;
  } status;


  // **** Internals ****
  logic [1:0]  sync;


  // ***************************************************************************
  // Assignments
  // ***************************************************************************

  assign acenable = control.enable;



  // ***************************************************************************
  // "dbus" Connection
  // ***************************************************************************

  always_comb
    begin
`ifdef VERILATOR //TODO
      dbus.sConnect( .id(ID), .rst(rst), .sdata(sdata), .ws(ws), .mdata(mdata), .adr(adr     ), .we(we), .re(re) );
`else
      dbus.sConnect( .id(ID), .rst(rst), .sdata(sdata), .ws(ws), .mdata(mdata), .adr(adr[1:0]), .we(we), .re(re) );
`endif
//      dbus.sConnect( ID, rst, sdata, ws, mdata, adr, we, re );
    end



  // ***************************************************************************
  // Register Access
  // ***************************************************************************

  // **** Register Write ****
  always_ff @( posedge clk )
    begin
      if ( rst )
        control <= 8'h00;
      else if ( (adr[1:0] == 2'b00) & we[0] )
        control <= mdata[7:0];
    end


  // **** Regiser Read ****
  always_comb
    begin: RegisterRead
      // - Local Variables -
      logic [7:0] data[0:3];   // Read access concatination.

      // - Setup read multiplexer -
      data = '{ control,
                status,
                8'h00,
                8'h00 };

      // - Connect "genbusif" -
      sdata = { 8'h00, data[ adr[1:0] ] };
      ws    = 1'b0;
    end



  // ***************************************************************************
  // Status
  // ***************************************************************************

  // **** Synchronization ****
  always_ff @( posedge clk )
    begin
      if ( rst )
        sync <= 2'b00;
      else if ( control.enable )
        sync <= {sync[0], acout};
    end

  always_comb
    begin
      // - Defaults -
      status = {$size(status){1'b0}};

      // - Set register values -
      status.acout = sync[1];
    end

endmodule // ac_dig
