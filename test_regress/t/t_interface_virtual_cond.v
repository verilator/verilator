// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface Bus;
  logic [15:0] data;
endinterface

module t;
  Bus intf ();
  virtual Bus vif;
  virtual Bus vif_arr[5];

  function logic get_vif(inout virtual Bus vif);
    vif = intf;
    return 0;
  endfunction

  initial begin
    if (get_vif(vif));
    while (get_vif(vif));
    do; while (get_vif(vif));
    for (int i = 0; get_vif(vif); i++);

    foreach (vif_arr[i]) begin
      if (vif_arr[i]) begin
        $display("vif_arr[%0d]=%p", i, vif_arr[i]);
      end
      else begin
        vif_arr[i] = intf;
      end
    end
  end

endmodule
