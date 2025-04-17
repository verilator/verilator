// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class ArrayStruct;
    /* verilator lint_off SIDEEFFECT */
    // Struct with an unpacked array
    typedef int arr_3_t[3];
    typedef int arr_4_t[4];
    typedef struct {
        rand arr_3_t arr_3;
        arr_4_t arr_4;
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

    constraint c_unpacked {
        foreach (s1.arr[i]) s1.arr[i] inside {1, 2, 3, 4};
        foreach (s1.arr_3[i]) s1.arr_3[i] inside {11, 22, 33, 44, 55};
    }
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
        s1.arr_3 = '{1, 2, 3};
        s1.arr_4 = '{0, 2, 3, 4};
        s2.arr = new[3];
        foreach(s2.arr[i]) begin
            s2.arr[i] = 'h0 + i;
        end
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

    function void print();
        foreach (s1.arr[i]) $display("s1.arr[%0d] = %0d", i, s1.arr[i]);
        foreach (s1.arr_3[i]) $display("s1.arr_3[%0d] = %0d", i, s1.arr_3[i]);
        foreach (s1.arr_4[i]) $display("s1.arr_4[%0d] = %0d", i, s1.arr_4[i]);
        foreach (s2.arr[i]) $display("s2.arr[%0d] = %0d", i, s2.arr[i]);
        foreach (s3.arr[i]) $display("s3.arr[%0d] = %0d", i, s3.arr[i]);
        foreach (s4.arr[i]) $display("s4.arr[\"%s\"] = %0d", i, s4.arr[i]);
        foreach (s5.arr[i, j]) $display("s5.arr[%0d][%0d] = %0d", i, j, s5.arr[i][j]);
        foreach (s6.mix_arr[i, j]) $display("s6.mix_arr[%0d][%0d] = %0d", i, j, s6.mix_arr[i][j]);
    endfunction

    // Self-test function to verify constraints
    function void self_test();
        foreach (s1.arr[i]) if (!(s1.arr[i] inside {1, 2, 3, 4})) $stop;
        foreach (s1.arr_3[i]) if (!(s1.arr_3[i] inside {11, 22, 33, 44, 55})) $stop;
        // Note: s1.arr_4[0] is not rand
        if ((s1.arr_4[0] != 0) || (s1.arr_4[1] != 2) || (s1.arr_4[2] != 3) || (s1.arr_4[3] != 4)) $stop;
        foreach (s2.arr[i]) if (!(s2.arr[i] inside {[10:20]})) $stop;
        foreach (s3.arr[i]) if (!(s3.arr[i] inside {[100:200]})) $stop;
        if (!(s4.arr["one"] inside {[10:50]})) $stop;
        if (!(s4.arr["two"] inside {[51:100]})) $stop;
        if (!(s4.arr["three"] inside {[101:150]})) $stop;
        foreach (s5.arr[i, j]) if (!(s5.arr[i][j] inside {[0:9]})) $stop;
        foreach (s6.mix_arr[i]) if (s6.mix_arr[i].size() == 0) $stop;
        foreach (s6.mix_arr[i, j]) if (!(s6.mix_arr[i][j] inside {[50:100]})) $stop;
    endfunction
    /* verilator lint_off SIDEEFFECT */
endclass

class StructArray;
    /* verilator lint_off WIDTHTRUNC */
    typedef struct {
        rand int arr[3];                    // static unpacked array
        rand int dyn[];                    // dynamic array
        rand int que[$];                   // queue
        rand int assoc[string];            // associative array with string key
        rand int a;
        rand bit [3:0] b;
        bit c;
    } struct_t;

    rand struct_t s_arr[2];

    constraint c_static {
        foreach (s_arr[i])
            foreach (s_arr[i].arr[j])
                s_arr[i].arr[j] inside {[0:9]};
    }

    constraint c_dyn {
        // foreach (s_arr[i])
            // s_arr[i].dyn.size() == 2;
        foreach (s_arr[i])
            foreach (s_arr[i].dyn[j])
                s_arr[i].dyn[j] inside {[10:19]};
    }

    constraint c_queue {
        // foreach (s_arr[i])
            // s_arr[i].que.size() == 2;
        foreach (s_arr[i])
            foreach (s_arr[i].que[j])
                s_arr[i].que[j] inside {[20:29]};
    }

    constraint c_assoc {
        foreach (s_arr[i]) {
            // s_arr[i].assoc.exists("x");
            // s_arr[i].assoc.exists("y");
            s_arr[i].assoc["x"] inside {[30:39]};
            s_arr[i].assoc["y"] inside {[30:39]};
        }
    }

    constraint c_other {
        foreach (s_arr[i]) s_arr[i].a inside {[40:50]};
    }

    function new();
        foreach (s_arr[i]) begin
            s_arr[i].dyn = new[2];
            s_arr[i].que = {0, 0};
            s_arr[i].assoc = '{"x": 0, "y": 0};

            foreach (s_arr[i].arr[j])
                s_arr[i].arr[j] = j;
            foreach (s_arr[i].dyn[j])
                s_arr[i].dyn[j] = 10 + j;
            foreach (s_arr[i].que[j])
                s_arr[i].que[j] = 20 + j;

            s_arr[i].assoc["x"] = i + 30;
            s_arr[i].assoc["y"] = i + 31;
            s_arr[i].a = 40 + i;
            s_arr[i].b = i;
            s_arr[i].c = i;
        end
    endfunction

    function void print();
        foreach (s_arr[i]) begin
            foreach (s_arr[i].arr[j])
                $display("s_arr[%0d].arr[%0d] = %0d", i, j, s_arr[i].arr[j]);
            foreach (s_arr[i].dyn[j])
                $display("s_arr[%0d].dyn[%0d] = %0d", i, j, s_arr[i].dyn[j]);
            foreach (s_arr[i].que[j])
                $display("s_arr[%0d].que[%0d] = %0d", i, j, s_arr[i].que[j]);

            $display("s_arr[%0d].assoc[\"x\"] = %0d", i, s_arr[i].assoc["x"]);
            $display("s_arr[%0d].assoc[\"y\"] = %0d", i, s_arr[i].assoc["y"]);
            $display("s_arr[%0d].a = %0d", i, s_arr[i].a);
            $display("s_arr[%0d].b = %0d", i, s_arr[i].b);
            $display("s_arr[%0d].c = %0d", i, s_arr[i].c);
        end
    endfunction

    function void self_test();
        foreach (s_arr[i]) begin
            foreach (s_arr[i].arr[j])
                if (!(s_arr[i].arr[j] inside {[0:9]})) $stop;
            foreach (s_arr[i].dyn[j])
                if (!(s_arr[i].dyn[j] inside {[10:19]})) $stop;
            foreach (s_arr[i].que[j])
                if (!(s_arr[i].que[j] inside {[20:29]})) $stop;
            if (!(s_arr[i].assoc.exists("x") && s_arr[i].assoc["x"] inside {[30:39]})) $stop;
            if (!(s_arr[i].assoc.exists("y") && s_arr[i].assoc["y"] inside {[30:39]})) $stop;
            if (!(s_arr[i].a inside {[40:50]})) $stop;
            if (i == 0 && s_arr[i].c != 0) $stop;
            if (i == 1 && s_arr[i].c != 1) $stop;
        end
    endfunction

    /* verilator lint_off WIDTHTRUNC */
endclass

module t_constraint_struct_complex;
    int success;
    ArrayStruct as_c;
    StructArray sa_c;
    initial begin
        as_c = new();
        sa_c = new();
        success = as_c.randomize();
        if (success != 1) $stop;
        as_c.self_test();
        // as_c.print();
        success = sa_c.randomize();
        if (success != 1) $stop;
        sa_c.self_test();
        // sa_c.print();
        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
