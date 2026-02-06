parameter int ELEN = 32;

class riscv_vector_cfg;
  rand int vec_fp;
  constraint vec_quad_widening_c {vec_fp == ELEN;}
endclass

class riscv_instr_gen_config;
  rand riscv_vector_cfg vector_cfg;
endclass

module t;
  riscv_instr_gen_config c;
  initial begin
    c = new;
    c.vector_cfg = new;
    c.randomize();
    $finish;
  end
endmodule
