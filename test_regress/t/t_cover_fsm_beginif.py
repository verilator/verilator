import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--cc --coverage-fsm'])
test.execute()

test.file_grep(test.obj_dir + "/coverage.dat", r"fsm_state")
test.file_grep(test.obj_dir + "/coverage.dat", r"fsm_arc")
test.file_grep(test.obj_dir + "/coverage.dat", r"ANY->S0")
test.file_grep(test.obj_dir + "/coverage.dat", r"reset_include")
test.file_grep(test.obj_dir + "/coverage.dat", r"S0->S1")
test.file_grep(test.obj_dir + "/coverage.dat", r"S0->S2")

test.passes()
