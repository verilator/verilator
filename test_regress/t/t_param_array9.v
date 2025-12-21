// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module p_i_match #(
    parameter type S_IS_T,
    parameter S_IS_T S_IS
) ();
endmodule

module ring #(
    parameter type I_T
) ();

  localparam int unsigned N_SS = (18 / 2) / 2;
  localparam int unsigned N_P_IS = (18 / 2) - 1;
  typedef int s_is_t[N_P_IS-1:0];

  function automatic s_is_t gen_s_is();
    for (int st = 0; st < N_SS; st++) begin
      for (int i = 0; i < 2; i++) begin
        if (st * 2 + i < N_P_IS) begin
          int delta = ((st + 1) * 2) + i;
          gen_s_is[st*2+i] = i;
        end
      end
    end
  endfunction

  localparam s_is_t S_IS = gen_s_is();

  p_i_match #(
      .S_IS_T(s_is_t),
      .S_IS(S_IS)
  ) p (
      .*
  );
endmodule

module t;
  typedef logic [4:0] i_t;
  ring #(.I_T(i_t)) dut (.*);
endmodule
