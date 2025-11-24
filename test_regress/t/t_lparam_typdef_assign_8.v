
package a_pkg;

endpackage

package cb;
   typedef struct packed {
      int unsigned XdatSize;     // raw packet data size
   } cfg_t;
endpackage

module a_mod();

   typedef struct packed {
      logic hdr_vld;
   } cmd_meta_t;

   typedef struct packed {
      cmd_meta_t meta;
   } cmd_beat_t;

   typedef logic [3:0] cc_index_t;

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
