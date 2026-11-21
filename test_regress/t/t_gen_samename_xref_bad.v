// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nick Brereton
// SPDX-License-Identifier: CC0-1.0

module leaf;
  int mem;
  function automatic int get();
    return mem;
  endfunction
endmodule

module core_a;
  int only_a;
endmodule

module core_b;
  int only_b;
  function automatic int fb();
    return 6;
  endfunction
endmodule

module mid #(
    parameter bit R = 1
);
  if (R) begin : g
    leaf u_a ();
    core_a u_core ();
    if (R) begin : h
      int h1;
    end
    else begin : h
      int h2;
    end
    begin : inner
      function automatic int get();
        return 1;
      endfunction
    end
  end
  else begin : g
    leaf u_b ();
    core_b u_core ();
    if (!R) begin : h
      int h0;
    end
    else begin : h
      int h3;
    end
    int last_only;
  end
endmodule

module noelse #(
    parameter bit R = 0
);
  if (R) begin : g
    function automatic int get();
      return 1;
    endfunction
    begin : inner
      function automatic int get();
        return 2;
      endfunction
    end
  end
endmodule

module t;
  mid u_r1 ();
  mid #(.R(0)) u_r0 ();
  noelse u_s ();

  initial begin
    $display("%0d", u_r1.g.u_b.mem);
    $display("%0d", u_r1.g.last_only);
    $display("%0d", u_r0.g.u_a.get());
    $display("%0d", u_r0.g.inner.get());
    $display("%0d", u_s.g.get());
    $display("%0d", u_s.g.inner.get());
    $display("%0d", u_r1.g.u_core.only_b);
    $display("%0d", u_r1.g.u_core.fb());
    $display("%0d", u_r1.g.h.h2);
    $display("%0d", u_r0.g.h.h1);
    $display("%0d", u_r0.g.h.h3);
  end
endmodule
