
package cb;
   typedef struct packed {
      int unsigned XdatSize;
   } cfg_t;
endpackage

module a_mod();

   typedef logic [3:0] cc_index_t;

   typedef struct packed {
      cc_index_t index;
      logic hdr_vld;
   } cmd_meta_t;

   typedef struct packed {
      cmd_meta_t meta;
   } cmd_beat_t;

    localparam cb::cfg_t cb_cfg = '{
        XdatSize:$bits(cmd_beat_t)
    };

endmodule

module top();

    a_mod a_mod_inst();

   initial begin
      #1;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
