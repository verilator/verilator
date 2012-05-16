// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

// Contributed by M W Lund, Atmel Corporation.

module adrdec
 #( parameter
      NSLAVES  = 2 )
 (
  // ***************************************************************************
  // Module Interface (interfaces, outputs, and inputs)
  // ***************************************************************************

  // **** Interfaces ****
  genbus_if.adrdec dbus

 );

  // ***************************************************************************
  // Address Decode
  // ***************************************************************************

//  const logic [15:0] adrmap[1:2] = '{}

  always_comb
    begin
      logic sel [1:NSLAVES];
      sel[1] = (dbus.s_adr[1][7:4] == 4'h0);
      sel[2] = (dbus.s_adr[2][7:4] == 4'h1);
//      sel[3] = (dbus.s_adr[3][7:4] == 4'h2);

      dbus.s_sel = sel;
//      for ( i = 1; i <= dbus.aNumSlaves; i++ )
//        begin
//          dbus.s_sel[i] = (dbus.s_adr[i] == adrmap[i]);
//        end
    end

endmodule // adrdec
