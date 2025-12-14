import vltest_bootstrap

test.scenarios('simulator')

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()
test.execute()
test.passes()
