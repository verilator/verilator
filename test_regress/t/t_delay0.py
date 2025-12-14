import vltest_bootstrap

test.scenarios('simulator')

test.compile(v_flags2=['--timing'])
test.execute()
test.passes()
