module top();
        event ready_to_finish;

        task automatic first();
                #300;
                ->ready_to_finish;
        endtask

        task automatic second();
                process job;
                int j = 0;
                int i = 0;

                fork
                        i = 5;
                        begin
                                #10;
                                job = process::self();
                        end
                        begin
                                while (j < 10) begin
                                        #5;
                                        j++;
                                end
                        end
                join_any;

                /* The first block should finish instantly, join_any exits */
                $display("After fork: i=%d, j=%d, job=%p", i, j, job);

                wait(j == 3);
                $display("After j wait: i=%d, j=%d, job=%p", i, j, job);

                // Now wait for the first task to finish
                @ready_to_finish;

                $display("After ready to finish: i=%d, j=%d, job=%p", i, j, job);

                $display("All done!");
                $finish();

        endtask

        initial begin
                fork
                        first();
                        second();
                        begin
                                #500;
                                $display("Should not reach this before $finish");
                                $stop;
                        end
                join_none

                $display("Everything has been started!");
        end

endmodule
