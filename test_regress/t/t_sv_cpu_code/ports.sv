// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.
// SPDX-License-Identifier: CC0-1.0

// Contributed by M W Lund, Atmel Corporation.

`ifdef VERILATOR  //TODO
 `define PACKED packed
`else
 `define  packed
`endif

module ports
 #( parameter
      ID = 1 )
 (
  // ***************************************************************************
  // Module Interface (interfaces, outputs, and inputs)
  // ***************************************************************************

  genbus_if.slave dbus,
  pads_if.mp_dig  padsif,

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


  // **** Interal Registers ****
  struct `PACKED
  {
    logic [7:0][1:0] in;
    logic [7:0]      dir;
    logic [7:0]      out;
    struct `PACKED
    {
    logic [7:2]      reserved;
    logic            pullupen;
    logic            slewlim;
    } cfg;
  } port [PORTID_A:PORTID_D];

  // ***************************************************************************
  // "dbus" Connection
  // ***************************************************************************

  always_comb
    begin: dbus_Connect
      dbus.sConnect( .id(ID), .rst(rst), .sdata(sdata), .ws(ws), .mdata(mdata), .adr(adr), .we(we), .re(re) );
    end



  // ***************************************************************************
  // Register Access
  // For PORTA...PORTD (Excluding I and O)
  // +0x00 DIR
  // +0x01 OUT
  // +0x02 IN
  // +0x03 CFG
  // ***************************************************************************

  always_comb begin padsif.Init(); end

  // **** Register Write ****
  always_ff @( posedge clk )
    begin
      // - Local Variables -
      integer i, j;

      // **** Setup Port Registers ****
      for ( j = PORTID_A; j <= PORTID_D; j++ )
        begin
          if ( padsif.IsPort( j ) )
            begin
              if ( ((adr[3:2] == j[1:0]) && (adr[1] == 1'b0)) | rst )
                begin
                  if ( we[0] )
                    port[j].dir <= mdata[7:0];
                  if ( we[1] )
                    port[j].out <= mdata[15:8];
                end
            end
          else
            begin
              port[j].dir <= 8'h00;
              port[j].out <= 8'h00;
            end
        end
    end


  // **** Regiser Read ****
  always_comb
    begin: RegisterRead
      // - Local Variables -
      integer i, j;
      logic [7:0] data [PORTID_D:PORTID_A][3:0];


      // **** Output to "dbus" ****

      // - Setup read multiplexer -
      for ( j = PORTID_A; j <= PORTID_D; j++ )
        begin
          if ( padsif.IsPort( j ) )
            data[j] = '{ port[j].dir, port[j].out, 8'h00, 8'h00 };
          else
            data[j] = '{ 8'h00, 8'h00, 8'h00, 8'h00 };
        end

      // - Connect "genbusif" -
      sdata = { 8'h00, data[ adr[3:2] ][ adr[1:0] ] };
      ws    = 1'b0;
    end



  // ***************************************************************************
  // Output
  // ***************************************************************************

  always_comb
    begin
      // - Local Variables -
      integer i, j;


      // **** Defaults ****
      for ( i = 1; i <= $size( pinout ); i++ )
        begin
          padsif.pullup_en    [i] = 1'b0;
          padsif.pulldown_en  [i] = 1'b0;
          padsif.output_en    [i] = 1'b0;
          padsif.output_val   [i] = 1'b0;
          padsif.slew_limit_en[i] = 1'b0;
          padsif.input_en     [i] = 1'b0;
        end


      // **** Connect to Pads ****
      for ( i = 1; i <= $size( pinout ); i++ )
        begin
          j = pinout[i].id;
          if ( PINID_D7 >= j )
            begin
              padsif.output_en [i] = port[j[4:3]].dir[j[2:0]];
              padsif.output_val[i] = port[j[4:3]].out[j[2:0]];
            end
        end
    end

endmodule // ports
