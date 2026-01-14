typedef struct {
  int unsigned   size_in_bytes;
} mem_region_t;

class riscv_load_store_base_instr_stream;
  mem_region_t    data_page;
  rand int           max_load_store_offset;
  constraint addr_c {
      max_load_store_offset == data_page.size_in_bytes;
  }
endclass

module t;
    riscv_load_store_base_instr_stream x;
    initial begin
      x = new;
      void'(x.randomize());
    end
endmodule
