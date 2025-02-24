// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

/*
// For pull request: Struct containing all array types
typedef struct {
    int unpacked_arr[3];     // Unpacked array
    int dynamic_arr[];       // Dynamic array
    int queue_arr[$];        // Queue
    int assoc_arr[string];   // Associative array (string index)
    int multi_dim_arr[2][3]; // Multi-dimensional array
    int mix_arr[3][];        // Mixed array (unpacked + dynamic)
} big_struct_t;

// For pull request: Randomized class for big_struct_t with self-test
class BigStructClass;
    rand big_struct_t big;

    // Constraints for all array types
    constraint c_unpacked { foreach (big.unpacked_arr[i]) big.unpacked_arr[i] inside {1, 2, 3, 4}; }
    constraint c_dynamic { big.dynamic_arr.size() == 3; foreach (big.dynamic_arr[i]) big.dynamic_arr[i] inside {[10:20]}; }
    constraint c_queue { big.queue_arr.size() inside {[2:5]}; foreach (big.queue_arr[i]) big.queue_arr[i] inside {[100:200]}; }
    constraint c_assoc {
        big.assoc_arr.num() == 3;
        big.assoc_arr.exists("one"); big.assoc_arr["one"] inside {[10:50]};
        big.assoc_arr.exists("two"); big.assoc_arr["two"] inside {[51:100]};
        big.assoc_arr.exists("three"); big.assoc_arr["three"] inside {[101:150]};
    }
    constraint c_multi_dim { foreach (big.multi_dim_arr[i, j]) big.multi_dim_arr[i][j] inside {[0:9]}; }
    constraint c_mix {
        foreach (big.mix_arr[i]) big.mix_arr[i].size() inside {[1:4]};
        foreach (big.mix_arr[i, j]) big.mix_arr[i][j] inside {[50:100]};
    }

    // Self-test function to verify constraints
    function void self_test();
        foreach (big.unpacked_arr[i]) if (!(big.unpacked_arr[i] inside {1, 2, 3, 4}))
            $stop;
        if (big.dynamic_arr.size() != 3)
            $stop;
        foreach (big.dynamic_arr[i]) if (!(big.dynamic_arr[i] inside {[10:20]}))
            $stop;
        if (!(big.queue_arr.size() inside {[2:5]}))
            $stop;
        foreach (big.queue_arr[i]) if (!(big.queue_arr[i] inside {[100:200]}))
            $stop;
        if (big.assoc_arr.num() != 3)
            $stop
        if (!big.assoc_arr.exists("one") || !(big.assoc_arr["one"] inside {[10:50]}))
            $stop;
        if (!big.assoc_arr.exists("two") || !(big.assoc_arr["two"] inside {[51:100]}))
            $stop;
        if (!big.assoc_arr.exists("three") || !(big.assoc_arr["three"] inside {[101:150]}))
            $stop;
        foreach (big.multi_dim_arr[i, j]) if (!(big.multi_dim_arr[i][j] inside {[0:9]}))
            $stop;
        foreach (big.mix_arr[i]) if (!(big.mix_arr[i].size() inside {[1:4]}))
            $stop;
        foreach (big.mix_arr[i, j]) if (!(big.mix_arr[i][j] inside {[50:100]}))
            $stop;
    endfunction
endclass

module t_constraint_struct_complex;
    initial begin
    BigStructClass big_struct_inst = new();

    repeat (5) begin // Run multiple randomizations
        if (!big_struct_inst.randomize())
        $stop;  // Stop if randomization fails

        $display("\n===== Randomized Test =====");
        $display("Unpacked Array: %p", big_struct_inst.big.unpacked_arr);
        $display("Dynamic Array: %p", big_struct_inst.big.dynamic_arr);
        $display("Queue: %p", big_struct_inst.big.queue_arr);
        $display("Associative Array: %p", big_struct_inst.big.assoc_arr);
        $display("Multi-Dimensional Array: %p", big_struct_inst.big.multi_dim_arr);
        $display("Mixed Array:");
        foreach (big_struct_inst.big.mix_arr[i])
        $display("  mix_arr[%0d] = %p", i, big_struct_inst.big.mix_arr[i]);

        // Perform self-test
        big_struct_inst.self_test();
    end

    $finish;
    end
endmodule

*/

// =========================
// For Debugging: t_constraint_struct_complex


class StructConstraintClass;
    /* verilator lint_off SIDEEFFECT */
    // Struct with an unpacked array
    typedef struct {
        rand int arr[3];
    } unpacked_struct_t;

    // Struct with a dynamic array
    typedef struct {
        rand int arr[];
    } dynamic_struct_t;

    // Struct with a queue
    typedef struct {
        rand int arr[$];
    } queue_struct_t;

    // Struct with an associative array (string as index)
    typedef struct {
        rand int arr[string];
    } associative_struct_t;

    // Struct with a multi-dimensional array
    typedef struct {
        rand int arr[2][3];
    } multi_dim_struct_t;

    // Struct with a mix of dynamic and unpacked arrays
    typedef struct {
        rand int mix_arr[3][];
    } mixed_struct_t;

    rand unpacked_struct_t s1;
    rand dynamic_struct_t s2;
    rand queue_struct_t s3;
    rand associative_struct_t s4;
    rand multi_dim_struct_t s5;
    rand mixed_struct_t s6;

    constraint c_unpacked { foreach (s1.arr[i]) s1.arr[i] inside {1, 2, 3, 4}; }
    constraint c_dynamic { foreach (s2.arr[i]) s2.arr[i] inside {[10:20]}; }
    constraint c_queue { foreach (s3.arr[i]) s3.arr[i] inside {[100:200]}; }
    constraint c_assoc {
        s4.arr["one"] inside {[10:50]};
        s4.arr["two"] inside {[51:100]};
        s4.arr["three"] inside {[101:150]};
    }
    constraint c_multi_dim { foreach (s5.arr[i, j]) s5.arr[i][j] inside {[0:9]}; }
    constraint c_mix {
        foreach (s6.mix_arr[i, j]) s6.mix_arr[i][j] inside {[50:100]};
    }

    function new();
        s1.arr = '{1, 2, 3};
        s2.arr = new[3];
        s2.arr = '{default:0};
        s3.arr.push_back(100);
        s3.arr.push_back(200);
        s3.arr.push_back(300);
        s4.arr["one"] = 1000;
        s4.arr["two"] = 2000;
        s4.arr["three"] = 3000;
        s5.arr = '{ '{default:0}, '{default:0} };
        foreach (s6.mix_arr[i]) begin
            s6.mix_arr[i] = new[i + 1];
        end
    endfunction

    // Self-test function to verify constraints
    function void self_test();
        foreach (s1.arr[i]) if (!(s1.arr[i] inside {1, 2, 3, 4})) begin
            $display("Error: s1.arr[%0d] = %0d is out of range", i, s1.arr[i]);
            $stop;
        end
        foreach (s2.arr[i]) if (!(s2.arr[i] inside {[10:20]})) begin
            $display("Error: s2.arr[%0d] = %0d is out of range", i, s2.arr[i]);
            $stop;
        end
        foreach (s3.arr[i]) if (!(s3.arr[i] inside {[100:200]})) begin
            $display("Error: s3.arr[%0d] = %0d is out of range", i, s3.arr[i]);
            $stop;
        end
        if (!(s4.arr["one"] inside {[10:50]})) begin
            $display("Error: s4.arr[\"one\"] = %0d is out of range", s4.arr["one"]);
            $stop;
        end
        if (!(s4.arr["two"] inside {[51:100]})) begin
            $display("Error: s4.arr[\"two\"] = %0d is out of range", s4.arr["two"]);
            $stop;
        end
        if (!(s4.arr["three"] inside {[101:150]})) begin
            $display("Error: s4.arr[\"three\"] = %0d is out of range", s4.arr["three"]);
            $stop;
        end
        foreach (s5.arr[i, j]) if (!(s5.arr[i][j] inside {[0:9]})) begin
            $display("Error: s5.arr[%0d][%0d] = %0d is out of range", i, j, s5.arr[i][j]);
            $stop;
        end
        foreach (s6.mix_arr[i]) if (s6.mix_arr[i].size() == 0) begin
            $display("Error: s6.mix_arr[%0d] is empty", i);
            $stop;
        end
        foreach (s6.mix_arr[i, j]) if (!(s6.mix_arr[i][j] inside {[50:100]})) begin
            $display("Error: s6.mix_arr[%0d][%0d] = %0d is out of range", i, j, s6.mix_arr[i][j]);
            $stop;
        end
    endfunction
    /* verilator lint_off SIDEEFFECT */
endclass

module t_constraint_struct_complex;
    int success;
    StructConstraintClass scc;
    initial begin
        scc = new();
        success = scc.randomize();
        if (success != 1) $stop;
        scc.self_test();
        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
