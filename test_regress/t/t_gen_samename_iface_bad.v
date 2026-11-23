// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nick Brereton
// SPDX-License-Identifier: CC0-1.0

interface bus_if;
  logic d;
  modport mp(input d);
endinterface

interface wrap_if #(
    parameter int X = 1
) (
    bus_if b
);
endinterface

module sink (
    bus_if b
);
endmodule

module ifc #(
    parameter bit R = 1
);
  wrap_if #(.X(2)) u_w (.b(g.bus));
  if (R) begin : g
    bus_if bus ();
    bus_if ba[2] ();
  end
  else begin : g
    bus_if bus ();
    bus_if ba[2] ();
  end
  case (R)
    1'b1: begin : c
      if (1) begin : n
        bus_if bus ();
      end
    end
    default: begin : c
      if (1) begin : n
        bus_if bus ();
      end
    end
  endcase
  for (genvar i = 0; i < 2; ++i) begin : f
    bus_if fb ();
    if (R) begin : g
      bus_if bus ();
    end
    else begin : g
      bus_if bus ();
    end
  end
  sink u_bus (.b(g.bus));
  sink u_mp (.b(g.bus.mp));
  sink u_arr (.b(g.ba[1]));
  sink u_case (.b(c.n.bus));
  sink u_for (.b(f[1].g.bus));
  sink u_loop (.b(f[1].fb));
endmodule

module t;
  ifc u_ifc ();
endmodule
