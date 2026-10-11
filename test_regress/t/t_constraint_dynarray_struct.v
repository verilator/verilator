// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {
  rand int value;
} Entry;

class StructArray;
  rand Entry values[];
  int pre_randomize_count;

  constraint c_size { values.size() == 3; }

  constraint c_values {
    values[0].value == 0;
    values[1].value == 31;
    values[2].value == 15;
  }

  function void pre_randomize();
    ++pre_randomize_count;
  endfunction
endclass

class InheritedStructArray extends StructArray;
  constraint c_inherited_value { values[2].value == 15; }
endclass

class AssocArrayControl;
  rand int values[int];

  constraint c_size { values.size() == 2; }

  constraint c_value { values[1] == 31; }
endclass

class OutOfBoundsArray;
  rand Entry values[];

  constraint c_size { values.size() == 1; }

  constraint c_value { values[1].value == 31; }
endclass

class ScalarArray;
  rand int values[];

  constraint c_size { values.size() == 3; }

  constraint c_values {
    values[0] == 0;
    values[1] == 31;
    values[2] == 15;
  }
endclass

class InheritedScalarArray extends ScalarArray;
endclass

module t;
  initial begin
    automatic int randomize_result;

    repeat (20) begin
      automatic StructArray struct_array = new;
      automatic InheritedStructArray inherited_struct_array = new;
      automatic StructArray inline_struct_array = new;
      automatic AssocArrayControl assoc_array = new;
      automatic InheritedScalarArray inherited_scalar_array = new;
      automatic ScalarArray scalar_array = new;

      randomize_result = struct_array.randomize();
      `checkd(randomize_result, 1)
      `checkd(struct_array.pre_randomize_count, 1)
      `checkd(struct_array.values.size(), 3)
      `checkd(struct_array.values[0].value, 0)
      `checkd(struct_array.values[1].value, 31)
      `checkd(struct_array.values[2].value, 15)

      randomize_result = inherited_struct_array.randomize();
      `checkd(randomize_result, 1)
      `checkd(inherited_struct_array.pre_randomize_count, 1)
      `checkd(inherited_struct_array.values.size(), 3)
      `checkd(inherited_struct_array.values[0].value, 0)
      `checkd(inherited_struct_array.values[1].value, 31)
      `checkd(inherited_struct_array.values[2].value, 15)

      inline_struct_array.values = new[3];
      randomize_result = inline_struct_array.randomize() with {
        values[1].value == 31;
      };
      `checkd(randomize_result, 1)
      `checkd(inline_struct_array.pre_randomize_count, 1)
      `checkd(inline_struct_array.values.size(), 3)
      `checkd(inline_struct_array.values[1].value, 31)

      assoc_array.values[1] = 0;
      assoc_array.values[2] = 0;
      assoc_array.values.rand_mode(1);
      randomize_result = assoc_array.randomize();
      `checkd(randomize_result, 1)
      `checkd(assoc_array.values.size(), 2)
      `checkd(assoc_array.values[1], 31)

      randomize_result = inherited_scalar_array.randomize();
      `checkd(randomize_result, 1)
      `checkd(inherited_scalar_array.values.size(), 3)
      `checkd(inherited_scalar_array.values[0], 0)
      `checkd(inherited_scalar_array.values[1], 31)
      `checkd(inherited_scalar_array.values[2], 15)

      randomize_result = scalar_array.randomize();
      `checkd(randomize_result, 1)
      `checkd(scalar_array.values.size(), 3)
      `checkd(scalar_array.values[0], 0)
      `checkd(scalar_array.values[1], 31)
      `checkd(scalar_array.values[2], 15)
    end

    begin
      automatic OutOfBoundsArray out_of_bounds_array = new;
      randomize_result = out_of_bounds_array.randomize();
      `checkd(randomize_result, 0)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
