// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

module t_foreach_array;
    // Define various structures to test foreach behavior
    int dyn_arr[][];
    int queue[$][$];
    int unpacked_arr [3:1][9:8];
    int associative_array_3d[string][string][string];

    int queue_unp[$][3];      // Outer dynamic queue with fixed-size inner arrays
    int unp_queue[3][$];      // Fixed-size outer array with dynamic inner queues
    int dyn_queue[][];        // Fully dynamic 2D array
    int queue_dyn[$][];       // Outer dynamic queue with dynamic inner queues
    int dyn_unp[][3];         // Dynamic outer array with fixed-size inner arrays
    int unp_dyn[3][];         // Fixed-size outer array with dynamic inner arrays

    // Define counter for various structures of array
    int count_que, exp_count_que;
    int count_dyn, exp_count_dyn;
    int count_unp, exp_count_unp;
    int count_assoc;
    int count_queue_unp, exp_count_queue_unp;
    int count_unp_queue, exp_count_unp_queue;
    int count_dyn_queue, exp_count_dyn_queue;
    int count_queue_dyn, exp_count_queue_dyn;
    int count_dyn_unp, exp_count_dyn_unp;
    int count_unp_dyn, exp_count_unp_dyn;

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

        queue_unp = '{'{1, 2, 3}, '{4, 5, 6}, '{7, 8, 9}};
        unp_queue[0] = '{10, 11};
        unp_queue[1] = '{12, 13, 14};
        unp_queue[2] = '{15};
        dyn_queue = '{'{16, 17}, '{18, 19, 20}};
        queue_dyn = '{'{21, 22}, '{23, 24, 25}};
        dyn_unp = '{'{26, 27, 28}, '{29, 30, 31}};
        unp_dyn[0] = '{32, 33};
        unp_dyn[1] = '{34, 35, 36};
        unp_dyn[2] = '{37};

        // Perform foreach loop counting and expected value calculation
        count_que = 0;
        foreach(queue[i, j]) count_que++;
        exp_count_que = 0;
        foreach(queue[i]) foreach(queue[i][j]) exp_count_que++;

        count_dyn = 0;
        foreach(dyn_arr[i, j]) count_dyn++;
        exp_count_dyn = 0;
        foreach(dyn_arr[i]) foreach(dyn_arr[i][j]) exp_count_dyn++;

        count_unp = 0;
        foreach(unpacked_arr[i, j]) count_unp++;
        exp_count_unp = 0;
        foreach(unpacked_arr[i]) foreach(unpacked_arr[i][j]) exp_count_unp++;

        count_assoc = 0;
        foreach(associative_array_3d[k1, k2, k3]) count_assoc++;

        count_queue_unp = 0;
        foreach (queue_unp[i, j]) count_queue_unp++;
        exp_count_queue_unp = 0;
        foreach (queue_unp[i]) foreach (queue_unp[i][j]) exp_count_queue_unp++;

        count_unp_queue = 0;
        foreach (unp_queue[i, j]) count_unp_queue++;
        exp_count_unp_queue = 0;
        foreach (unp_queue[i]) foreach (unp_queue[i][j]) exp_count_unp_queue++;

        count_dyn_queue = 0;
        foreach (dyn_queue[i, j]) count_dyn_queue++;
        exp_count_dyn_queue = 0;
        foreach (dyn_queue[i]) foreach (dyn_queue[i][j]) exp_count_dyn_queue++;

        count_queue_dyn = 0;
        foreach (queue_dyn[i, j]) count_queue_dyn++;
        exp_count_queue_dyn = 0;
        foreach (queue_dyn[i]) foreach (queue_dyn[i][j]) exp_count_queue_dyn++;

        count_dyn_unp = 0;
        foreach (dyn_unp[i, j]) count_dyn_unp++;
        exp_count_dyn_unp = 0;
        foreach (dyn_unp[i]) foreach (dyn_unp[i][j]) exp_count_dyn_unp++;

        count_unp_dyn = 0;
        foreach (unp_dyn[i, j]) count_unp_dyn++;
        exp_count_unp_dyn = 0;
        foreach (unp_dyn[i]) foreach (unp_dyn[i][j]) exp_count_unp_dyn++;

        // Verification checks
        if (count_que != 6 || count_que != exp_count_que) $stop;
        if (count_dyn != 12 || count_dyn != exp_count_dyn) $stop;
        if (count_unp != 6 || count_unp != exp_count_unp) $stop;
        if (count_assoc != 9) $stop;
        if (count_queue_unp != exp_count_queue_unp) $stop;
        if (count_unp_queue != exp_count_unp_queue) $stop;
        if (count_dyn_queue != exp_count_dyn_queue) $stop;
        if (count_queue_dyn != exp_count_queue_dyn) $stop;
        if (count_dyn_unp != exp_count_dyn_unp) $stop;
        if (count_unp_dyn != exp_count_unp_dyn) $stop;

        $write("*-* All Finished *-*\\n");
        $finish;
    end

endmodule
