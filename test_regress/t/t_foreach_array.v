// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t_foreach_array;
  // Define various structures to test foreach behavior
  int dyn_arr[][];
  int queue[$][$];
  int unpacked_arr[3:1][9:8];
  int associative_array_3d[string][string][string];

  int queue_unp[$][3];  // Outer dynamic queue with fixed-size inner arrays
  int unp_queue[3][$];  // Fixed-size outer array with dynamic inner queues
  int dyn_queue[][];  // Fully dynamic 2D array
  int queue_dyn[$][];  // Outer dynamic queue with dynamic inner queues
  int dyn_unp[][3];  // Dynamic outer array with fixed-size inner arrays
  int unp_dyn[3][];  // Fixed-size outer array with dynamic inner arrays

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

  // Queue/dynamic dimension after two or more fixed dimensions (#8891)
  int unp_unp_queue[3][3][$];
  int unp_unp_dyn[2][3][];
  int unp_queue_unp[2][$][3];
  int ranged_queue[3:2][4:3][$];
  int unp_unp_assoc[2][2][int];
  int queue_unp_queue[$][2][$];
  int neg_queue[-1:0][2:1][$];

  initial begin
    int count, exp_count;
    int sum, exp_sum;

    unp_unp_queue[0][0] = '{1, 2, 3};
    unp_unp_queue[1][2] = '{4, 5};
    unp_unp_queue[2][1] = '{6, 7};
    count = 0;
    sum = 0;
    foreach (unp_unp_queue[i, j, k]) begin
      ++count;
      sum += unp_unp_queue[i][j][k];
    end
    exp_count = 0;
    exp_sum = 0;
    foreach (unp_unp_queue[i])
    foreach (unp_unp_queue[i][j])
    foreach (unp_unp_queue[i][j][k]) begin
      ++exp_count;
      exp_sum += unp_unp_queue[i][j][k];
    end
    `checkd(exp_count, 7);
    `checkd(count, exp_count);
    `checkd(exp_sum, 28);
    `checkd(sum, exp_sum);

    unp_unp_dyn[0][1] = '{1, 2};
    unp_unp_dyn[1][0] = '{3};
    unp_unp_dyn[1][2] = '{4, 5, 6};
    count = 0;
    sum = 0;
    foreach (unp_unp_dyn[i, j, k]) begin
      ++count;
      sum += unp_unp_dyn[i][j][k];
    end
    exp_count = 0;
    exp_sum = 0;
    foreach (unp_unp_dyn[i])
    foreach (unp_unp_dyn[i][j])
    foreach (unp_unp_dyn[i][j][k]) begin
      ++exp_count;
      exp_sum += unp_unp_dyn[i][j][k];
    end
    `checkd(exp_count, 6);
    `checkd(count, exp_count);
    `checkd(exp_sum, 21);
    `checkd(sum, exp_sum);

    unp_queue_unp[0] = '{'{1, 2, 3}, '{4, 5, 6}};
    unp_queue_unp[1] = '{'{7, 8, 9}};
    count = 0;
    sum = 0;
    foreach (unp_queue_unp[i, j, k]) begin
      ++count;
      sum += unp_queue_unp[i][j][k];
    end
    `checkd(count, 9);
    `checkd(sum, 45);

    ranged_queue[3][3] = '{1, 2};
    ranged_queue[2][4] = '{3};
    count = 0;
    sum = 0;
    foreach (ranged_queue[i, j, k]) begin
      ++count;
      sum += ranged_queue[i][j][k];
    end
    `checkd(count, 3);
    `checkd(sum, 6);

    queue_unp_queue = '{'{'{1}, '{2, 3}}, '{'{}, '{4, 5, 6}}};
    count = 0;
    sum = 0;
    foreach (queue_unp_queue[i, j, k]) begin
      ++count;
      sum += queue_unp_queue[i][j][k];
    end
    `checkd(count, 6);
    `checkd(sum, 21);

    neg_queue[-1][2] = '{1, 2};
    neg_queue[0][1] = '{3};
    count = 0;
    sum = 0;
    foreach (neg_queue[i, j, k]) begin
      ++count;
      sum += neg_queue[i][j][k];
    end
    `checkd(count, 3);
    `checkd(sum, 6);

    unp_unp_assoc[0][1][5] = 1;
    unp_unp_assoc[1][0][7] = 2;
    unp_unp_assoc[1][0][9] = 3;
    count = 0;
    sum = 0;
    foreach (unp_unp_assoc[i, j, k]) begin
      ++count;
      sum += unp_unp_assoc[i][j][k];
    end
    `checkd(count, 3);
    `checkd(sum, 6);
  end

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
    foreach (queue[i, j]) count_que++;
    exp_count_que = 0;
    foreach (queue[i]) foreach (queue[i][j]) exp_count_que++;

    count_dyn = 0;
    foreach (dyn_arr[i, j]) count_dyn++;
    exp_count_dyn = 0;
    foreach (dyn_arr[i]) foreach (dyn_arr[i][j]) exp_count_dyn++;

    count_unp = 0;
    foreach (unpacked_arr[i, j]) count_unp++;
    exp_count_unp = 0;
    foreach (unpacked_arr[i]) foreach (unpacked_arr[i][j]) exp_count_unp++;

    count_assoc = 0;
    foreach (associative_array_3d[k1, k2, k3]) count_assoc++;

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
    `checkd(count_que, 6);
    `checkd(count_que, exp_count_que);
    `checkd(count_dyn, 12);
    `checkd(count_dyn, exp_count_dyn);
    `checkd(count_unp, 6);
    `checkd(count_unp, exp_count_unp);
    `checkd(count_assoc, 9);
    `checkd(count_queue_unp, exp_count_queue_unp);
    `checkd(count_unp_queue, exp_count_unp_queue);
    `checkd(count_dyn_queue, exp_count_dyn_queue);
    `checkd(count_queue_dyn, exp_count_queue_dyn);
    `checkd(count_dyn_unp, exp_count_dyn_unp);
    `checkd(count_unp_dyn, exp_count_unp_dyn);

    $write("*-* All Finished *-*\\n");
    $finish;
  end

endmodule
