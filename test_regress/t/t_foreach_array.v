// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

module t_foreach_array;

    int dyn_arr[][];
    int queue[$][$];
    int unpacked_arr [3:1][9:8];
    int associative_array_3d[string][string][string];

    int count_que;
    int exp_count_que;
    int count_dyn;
    int exp_count_dyn;
    int count_unp;
    int exp_count_unp;
    int count_assoc;

    string k1, k2, k3;

    initial begin
        // Initialize
        queue = '{'{1, 2, 3}, '{4, 5}, '{6}};
        dyn_arr = '{'{1, 2, 3}, '{4, 5, 6, 0, 10}, '{6, 7, 8, 9}};
        associative_array_3d["key1"]["subkey1"]["subsubkey1"] = 1;
        associative_array_3d["key1"]["subkey1"]["subsubkey2"] = 2;
        associative_array_3d["key1"]["subkey2"]["subsubkey1"] = 3;
        associative_array_3d["key1"]["subkey3"]["subsubkey1"] = 4;
        associative_array_3d["key1"]["subkey3"]["subsubkey2"] = 5;
        associative_array_3d["key1"]["subkey3"]["subsubkey3"] = 6;
        associative_array_3d["key2"]["subkey1"]["subsubkey1"] = 7;
        associative_array_3d["key2"]["subkey1"]["subsubkey2"] = 8;
        associative_array_3d["key2"]["subkey3"]["subsubkey1"] = 9;

        count_que = 0;

        foreach(queue[i, j]) begin
            count_que++;
        end

        exp_count_que = 0;
        foreach(queue[i]) begin
            foreach(queue[i][j]) begin
                exp_count_que++;
            end
        end

        count_dyn = 0;

        foreach(dyn_arr[i, j]) begin
            count_dyn++;
        end

        exp_count_dyn = 0;

        foreach(dyn_arr[i]) begin
            foreach(dyn_arr[i][j]) begin
                exp_count_dyn++;
            end
        end

        count_unp = 0;

        foreach(unpacked_arr[i, j]) begin
            count_unp++;
        end

        exp_count_unp = 0;

        foreach(unpacked_arr[i]) begin
            foreach(unpacked_arr[i][j]) begin
                exp_count_unp++;
            end
        end

        count_assoc = 0;

        foreach(associative_array_3d[k1, k2, k3]) begin
            count_assoc++;
        end

        if (count_que != 6 || count_que != exp_count_que) $stop;
        if (count_dyn != 12 || count_dyn != exp_count_dyn) $stop;
        if (count_unp != 6 || count_unp != exp_count_unp) $stop;
        if (count_assoc != 9) $stop;

        $write("*-* All Finished *-*\\n");
        $finish;
    end

endmodule
