// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface Bus;
  logic [15:0] data;
endinterface

module t;
  Bus intf ();
  virtual Bus vif;

  function logic get_vif(inout virtual Bus vif);
    vif = intf;
    return 0;
  endfunction

  initial begin
    if (get_vif(vif));
    while (get_vif(vif));
    do ; while (get_vif(vif));
    for (int i = 0; get_vif(vif); i++);
  end

endmodule
