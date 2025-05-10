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
        rand int a;
        rand bit [3:0] b;
        bit c;
    } struct_t;

    rand struct_t s_arr[2];
    rand struct_t s_2d_arr[2][3];
    rand struct_t s_dyn_arr[];
    rand struct_t s_que_arr[$];
    rand struct_t s_assoc_arr[string];
    rand struct_t s_assoc_arr_2[bit[5:0]];

    constraint c_arr {
        foreach (s_arr[i])
            foreach (s_arr[i].arr[j])
                s_arr[i].arr[j] inside {[0:9]};
        foreach (s_2d_arr[i, j])
            foreach (s_2d_arr[i][j].arr[k])
                s_2d_arr[i][j].arr[k] inside {[9:19]};
        foreach (s_dyn_arr[i])
            foreach (s_dyn_arr[i].arr[j])
                s_dyn_arr[i].arr[j] inside {[19:29]};
        foreach (s_que_arr[i])
            foreach (s_que_arr[i].arr[j])
                s_que_arr[i].arr[j] inside {[29:39]};
        foreach (s_assoc_arr[i])
            foreach (s_assoc_arr[i].arr[j])
                s_assoc_arr[i].arr[j] inside {[39:49]};
        foreach (s_assoc_arr_2[i])
            foreach (s_assoc_arr_2[i].arr[j])
                s_assoc_arr_2[i].arr[j] inside {[49:59]};
    }

    constraint c_others {
        foreach (s_arr[i]) s_arr[i].a inside {[40:50]};
        foreach (s_arr[i]) s_arr[i].b inside {[0:7]};

        foreach (s_2d_arr[i, j]) s_2d_arr[i][j].a inside {[50:60]};

        foreach (s_dyn_arr[i]) s_dyn_arr[i].a inside {[60:70]};

        foreach (s_que_arr[i]) s_que_arr[i].a inside {[70:80]};

        foreach (s_assoc_arr[i]) s_assoc_arr[i].a inside {[80:90]};

        foreach (s_assoc_arr_2[i]) s_assoc_arr_2[i].a inside {[90:100]};
    }

    function new();

        foreach (s_arr[i]) begin
            foreach (s_arr[i].arr[j])
                s_arr[i].arr[j] = j;
            s_arr[i].a = 40 + i;
            s_arr[i].b = i;
            s_arr[i].c = 0;
        end

        foreach (s_2d_arr[i, j]) begin
            foreach (s_2d_arr[i][j].arr[k])
                s_2d_arr[i][j].arr[k] = k + 10;
            s_2d_arr[i][j].a = 50 + i + j;
            s_2d_arr[i][j].b = i + j;
            s_2d_arr[i][j].c = 0;
        end

        foreach (s_dyn_arr[i]) begin
            s_dyn_arr = new[3];
            foreach (s_dyn_arr[i].arr[j])
                s_dyn_arr[i].arr[j] = j + 20;
            s_dyn_arr[i].a = 60 + i;
            s_dyn_arr[i].b = i;
            s_dyn_arr[i].c = 0;
        end

        for (int i = 0; i < 3; i++) begin
            s_que_arr.push_back('{arr: '{30, 31, 32}, a: 70 + i, b: i, c: 0});
        end

        // Associative array with string index
        foreach (s_assoc_arr["x"].arr[j])
            s_assoc_arr["x"].arr[j] = j + 40;
        foreach (s_assoc_arr["y"].arr[j])
            s_assoc_arr["y"].arr[j] = j + 50;
        foreach (s_assoc_arr["long_string_index"].arr[j])
            s_assoc_arr["long_string_index"].arr[j] = j + 60;
        s_assoc_arr["x"].a = 80;
        s_assoc_arr["x"].b = 0;
        s_assoc_arr["x"].c = 0;
        s_assoc_arr["y"].a = 90;
        s_assoc_arr["y"].b = 1;
        s_assoc_arr["y"].c = 0;
        s_assoc_arr["long_string_index"].a = 100;
        s_assoc_arr["long_string_index"].b = 2;
        s_assoc_arr["long_string_index"].c = 0;

        foreach (s_assoc_arr_2[6'd30].arr[j])
            s_assoc_arr_2[6'd30].arr[j] = j + 70;
        foreach (s_assoc_arr_2[6'd7].arr[j])
            s_assoc_arr_2[6'd7].arr[j] = j + 80;
        s_assoc_arr_2[6'd30].a = 90;
        s_assoc_arr_2[6'd30].b = 0;
        s_assoc_arr_2[6'd30].c = 0;
        s_assoc_arr_2[6'd7].a = 100;
        s_assoc_arr_2[6'd7].b = 1;
        s_assoc_arr_2[6'd7].c = 0;

    endfunction

    function void print();

        foreach (s_arr[i]) begin
            foreach (s_arr[i].arr[j])
                $display("s_arr[%0d].arr[%0d] = %0d", i, j, s_arr[i].arr[j]);
            $display("s_arr[%0d].a = %0d", i, s_arr[i].a);
            $display("s_arr[%0d].b = %0d", i, s_arr[i].b);
            $display("s_arr[%0d].c = %0d", i, s_arr[i].c);
        end

        foreach (s_2d_arr[i, j]) begin
            foreach (s_2d_arr[i][j].arr[k])
                $display("s_2d_arr[%0d][%0d].arr[%0d] = %0d", i, j, k, s_2d_arr[i][j].arr[k]);
            $display("s_2d_arr[%0d][%0d].a = %0d", i, j, s_2d_arr[i][j].a);
            $display("s_2d_arr[%0d][%0d].b = %0d", i, j, s_2d_arr[i][j].b);
            $display("s_2d_arr[%0d][%0d].c = %0d", i, j, s_2d_arr[i][j].c);
        end

        foreach (s_dyn_arr[i]) begin
            foreach (s_dyn_arr[i].arr[j])
                $display("s_dyn_arr[%0d].arr[%0d] = %0d", i, j, s_dyn_arr[i].arr[j]);
            $display("s_dyn_arr[%0d].a = %0d", i, s_dyn_arr[i].a);
            $display("s_dyn_arr[%0d].b = %0d", i, s_dyn_arr[i].b);
            $display("s_dyn_arr[%0d].c = %0d", i, s_dyn_arr[i].c);
        end

        foreach (s_que_arr[i]) begin
            foreach (s_que_arr[i].arr[j])
                $display("s_que_arr[%0d].arr[%0d] = %0d", i, j, s_que_arr[i].arr[j]);
            $display("s_que_arr[%0d].a = %0d", i, s_que_arr[i].a);
            $display("s_que_arr[%0d].b = %0d", i, s_que_arr[i].b);
            $display("s_que_arr[%0d].c = %0d", i, s_que_arr[i].c);
        end

        foreach (s_assoc_arr["x"].arr[j])
            $display("s_assoc_arr[x].arr[%0d] = %0d", j, s_assoc_arr["x"].arr[j]);
        $display("s_assoc_arr[x].a = %0d", s_assoc_arr["x"].a);
        $display("s_assoc_arr[x].b = %0d", s_assoc_arr["x"].b);
        $display("s_assoc_arr[x].c = %0d", s_assoc_arr["x"].c);
        foreach (s_assoc_arr["y"].arr[j])
            $display("s_assoc_arr[y].arr[%0d] = %0d", j, s_assoc_arr["y"].arr[j]);
        $display("s_assoc_arr[y].a = %0d", s_assoc_arr["y"].a);
        $display("s_assoc_arr[y].b = %0d", s_assoc_arr["y"].b);
        $display("s_assoc_arr[y].c = %0d", s_assoc_arr["y"].c);
        foreach (s_assoc_arr["long_string_index"].arr[j])
            $display("s_assoc_arr[long_string_index].arr[%0d] = %0d", j, s_assoc_arr["long_string_index"].arr[j]);
        $display("s_assoc_arr[long_string_index].a = %0d", s_assoc_arr["long_string_index"].a);
        $display("s_assoc_arr[long_string_index].b = %0d", s_assoc_arr["long_string_index"].b);
        $display("s_assoc_arr[long_string_index].c = %0d", s_assoc_arr["long_string_index"].c);

        foreach (s_assoc_arr_2[6'd30].arr[j])
            $display("s_assoc_arr_2[30].arr[%0d] = %0d", j, s_assoc_arr_2[6'd30].arr[j]);
        $display("s_assoc_arr_2[30].a = %0d", s_assoc_arr_2[6'd30].a);
        $display("s_assoc_arr_2[30].b = %0d", s_assoc_arr_2[6'd30].b);
        $display("s_assoc_arr_2[30].c = %0d", s_assoc_arr_2[6'd30].c);
        foreach (s_assoc_arr_2[6'd7].arr[j])
            $display("s_assoc_arr_2[7].arr[%0d] = %0d", j, s_assoc_arr_2[6'd7].arr[j]);
        $display("s_assoc_arr_2[7].a = %0d", s_assoc_arr_2[6'd7].a);
        $display("s_assoc_arr_2[7].b = %0d", s_assoc_arr_2[6'd7].b);
        $display("s_assoc_arr_2[7].c = %0d", s_assoc_arr_2[6'd7].c);

    endfunction

    function void self_test();

        foreach (s_arr[i]) begin
            foreach (s_arr[i].arr[j])
                if (!(s_arr[i].arr[j] inside {[0:9]})) $stop;
            if (!(s_arr[i].a inside {[40:50]})) $stop;
        end

        foreach (s_2d_arr[i, j]) begin
            foreach (s_2d_arr[i][j].arr[k])
                if (!(s_2d_arr[i][j].arr[k] inside {[9:19]})) $stop;
            if (!(s_2d_arr[i][j].a inside {[50:60]})) $stop;
        end

        foreach (s_dyn_arr[i]) begin
            foreach (s_dyn_arr[i].arr[j])
                if (!(s_dyn_arr[i].arr[j] inside {[19:29]})) $stop;
            if (!(s_dyn_arr[i].a inside {[60:70]})) $stop;
        end

        foreach (s_que_arr[i]) begin
            foreach (s_que_arr[i].arr[j])
                if (!(s_que_arr[i].arr[j] inside {[29:39]})) $stop;
            if (!(s_que_arr[i].a inside {[70:80]})) $stop;
        end

        foreach (s_assoc_arr["x"].arr[j])
            if (!(s_assoc_arr["x"].arr[j] inside {[39:49]})) $stop;
        if (!(s_assoc_arr["x"].a inside {[80:90]})) $stop;
        foreach (s_assoc_arr["y"].arr[j])
            if (!(s_assoc_arr["y"].arr[j] inside {[39:49]})) $stop;
        if (!(s_assoc_arr["y"].a inside {[80:90]})) $stop;
        foreach (s_assoc_arr["long_string_index"].arr[j])
            if (!(s_assoc_arr["long_string_index"].arr[j] inside {[39:49]})) $stop;
        if (!(s_assoc_arr["long_string_index"].a inside {[80:90]})) $stop;

        foreach (s_assoc_arr_2[6'd30].arr[j])
            if (!(s_assoc_arr_2[6'd30].arr[j] inside {[49:59]})) $stop;
        if (!(s_assoc_arr_2[6'd30].a inside {[90:100]})) $stop;
        foreach (s_assoc_arr_2[6'd7].arr[j])
            if (!(s_assoc_arr_2[6'd7].arr[j] inside {[49:59]})) $stop;
        if (!(s_assoc_arr_2[6'd7].a inside {[90:100]})) $stop;

    endfunction

    /* verilator lint_off WIDTHTRUNC */
endclass

class MixedStructure;
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
        foreach (s_arr[i])
            foreach (s_arr[i].dyn[j])
                s_arr[i].dyn[j] inside {[10:19]};
    }

    constraint c_queue {
        foreach (s_arr[i])
            foreach (s_arr[i].que[j])
                s_arr[i].que[j] inside {[20:29]};
    }

    constraint c_assoc {
        foreach (s_arr[i]) {
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
    MixedStructure mixed_c;

    initial begin
        as_c = new();
        sa_c = new();
        mixed_c = new();

        success = as_c.randomize();
        if (success != 1) $stop;
        as_c.self_test();
        // as_c.print();
        // $display(" ArrayStruct passed! \n");

        success = sa_c.randomize();
        if (success != 1) $stop;
        sa_c.self_test();
        // sa_c.print();
        // $display(" StructArray passed! \n");

        success = mixed_c.randomize();
        if (success != 1) $stop;
        mixed_c.self_test();
        // mixed_c.print();
        // $display(" MixedStructure passed! \n");

        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
