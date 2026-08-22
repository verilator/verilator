// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Arkadiusz Kozdra
// SPDX-License-Identifier: CC0-1.0

// See also t_interface_virtual.v

interface PBus;
  logic req, grant;
  logic [7:0] addr, data;
  modport phy(input addr, ref data);
endinterface

interface QBus;
endinterface

typedef virtual PBus vpbus_t;

module t;

  PBus p8 ();
  QBus q8 ();
  vpbus_t v8;
  virtual PBus.phy v8_phy;
  logic data;

  initial begin
    v8 = p8;
    p8 = v8;  // error
    v8 = q8;  // error
    v8_phy = p8;
    v8_phy = v8;
    v8_phy = p8.phy;
    v8 = v8_phy;  // error
    v8 = p8.phy;  // error
    data = p8.phy;  // error
    data = v8_phy;  // error
    data = v8;  // error
    data = p8;  // error
    v8 = data;  // error
    v8.grant = 1'b1;

    $display("q8.grant=", p8.grant, " v8.grant=", v8.grant, v8_phy.addr, v8.gran);

    $write("*-* All Finished *-*\n");
    $finish;
  end

  PBus p8_array[2] ();
  QBus q8_array[2] ();
  virtual PBus v8_array[2];
  virtual PBus v8_array3[3];

  function automatic void take_vif(input virtual PBus.phy vif);
  endfunction

  function automatic void take_ref_vif(ref virtual PBus.phy vif);
  endfunction

  function automatic void take_const_ref_vif(const ref virtual PBus.phy vif);
  endfunction

  function automatic void take_vif_array(input virtual PBus.phy vifs[2]);
  endfunction

  function automatic void take_ref_vif_array(ref virtual PBus.phy vifs[2]);
  endfunction

  function automatic void take_const_ref_vif_array(const ref virtual PBus.phy vifs[2]);
  endfunction

  initial begin
    take_vif(q8);
    take_ref_vif(v8);
    take_ref_vif(p8);
    take_const_ref_vif(v8);
    take_vif_array(q8_array);
    take_ref_vif_array(v8_array);
    take_ref_vif_array(p8_array);
    take_const_ref_vif_array(v8_array);
    take_vif(v8_array);
    take_vif_array(v8);
    take_vif_array(v8_array3);
  end
endmodule
