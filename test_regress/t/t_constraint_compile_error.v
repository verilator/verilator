package riscv_instr_pkg;
    typedef struct {
      int unsigned   size_in_bytes;  
    } mem_region_t;

    class riscv_mem_access_stream;
      int             max_data_page_id;
      mem_region_t    data_page[];
    endclass

    class riscv_load_store_base_instr_stream extends riscv_mem_access_stream;
      rand int unsigned  data_page_id;
      rand int   rs1_reg;
      rand int           max_load_store_offset;
      constraint addr_c {
        foreach (data_page[i]) {
          if (i == data_page_id) {
            max_load_store_offset == data_page[i].size_in_bytes;
          }
        }
      }
    endclass

    class riscv_multi_page_load_store_instr_stream;
      riscv_load_store_base_instr_stream load_store_instr_stream;
      function void post_randomize();
        void'(load_store_instr_stream.randomize());
      endfunction
    endclass
endpackage

module t;
endmodule
