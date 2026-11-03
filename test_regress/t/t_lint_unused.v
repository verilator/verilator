// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off UNOPTPUBLIC

`define STRINGIFY(x) `"x`"

module t (  /*AUTOARG*/
    // Outputs
    out,
    // Inputs
    in
);

  input in;  // inputs don't get flagged as undriven
  output out;  // outputs don't get flagged as unused

  sub sub ();
  class_data class_data ();

  // Check we don't warn about unused UDP signals
  udp_mux2 udpsub (
      out,
      in,
      in,
      in
  );

  // Check ignoreds mark as used
  reg sysused;
  initial $bboxed(sysused);

  // Check file IO.  The fopen is the "driver" all else a usage.
  integer infile;
  integer outfile;
  initial begin
    outfile = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/open.log"}, "w");
    $fwrite(outfile, "1\n");
    $fclose(outfile);
    infile = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/open.log"}, "r");
    if ($fgetc(infile) != "1") begin
    end
  end

  wire _unused_ok;

endmodule

module class_data;

  // Member selections must track the field, in addition to the object handle (#8957).
  class test;
    int i;
  endclass

  test t = new();
  initial begin
    t.i = 2;
    $display("t.i = %h", t.i);
  end

  class base;
    int written_outside;
    int read_outside;
    int updated_outside;

    function int read_field();
      return written_outside;
    endfunction

    function void write_field();
      read_outside = 3;
    endfunction
  endclass

  class derived extends base;
  endclass

  initial begin
    automatic derived obj = new();
    obj.written_outside = 4;
    $display("%0d", obj.read_field());
    obj.write_field();
    $display("%0d", obj.read_outside);
    obj.updated_outside++;
  end

  class indexed_fields;
    bit [6:0] data;
    bit [2:0] index;
    bit [1:0][6:0] packed_data;
    bit row;
    bit [6:0] values[3];
  endclass

  class holder;
    indexed_fields child;
    bit [1:0] object_index;
  endclass

  initial begin
    automatic indexed_fields objects[3];
    automatic bit [1:0] object_index = 1;
    automatic holder obj = new();
    obj.object_index = 1;
    objects[object_index] = new();
    objects[object_index].data = '0;
    objects[object_index].index = 3'd1;
    objects[object_index].data[objects[object_index].index] = 1'b1;
    $display("%h", objects[object_index].data[objects[object_index].index]);
    $display("%h", objects[obj.object_index].data[0]);
    objects[object_index].packed_data = '0;
    objects[object_index].row = 1'b1;
    objects[object_index].packed_data[objects[object_index].row][2] = 1'b1;
    $display("%h", objects[object_index].packed_data[objects[object_index].row][2]);
    objects[object_index].values[object_index][0] = 1'b1;
    $display("%h", objects[object_index].values[object_index][0]);
    obj.child = new();
    obj.child.data = '0;
    obj.child.index = 3'd2;
    obj.child.data[2]++;
    $display("%h", obj.child.data[2]);
  end

endmodule

module sub;

  wire pub  /*verilator public*/;  // Ignore publics

endmodule

primitive udp_mux2(q, a, b, s);
  output q;
  input a, b, s;
  table
    //a b  s  :  out
    1 ? 0 : 1;
    0 ? 0 : 0;
    ? 1 1 : 1;
    ? 0 1 : 0;
    0 0 x : 0;
    1 1 x : 1;
  endtable
endprimitive
