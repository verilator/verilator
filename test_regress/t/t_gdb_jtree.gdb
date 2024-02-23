# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

watch v3Global.m_rootp
run
python
try: gdb.execute("jtree v3Global.m_rootp")
except Exception: exit(1)
try: gdb.execute("jtree v3Global.m_rootp v3Global.m_rootp")
except Exception: exit(1)

# stash and use stashed dump
try: gdb.execute("jstash v3Global.m_rootp")
except Exception: exit(1)
# we assume that stash will end up in $1 (we can't use gdb.history_count() since it is not available in older gdb)
try: gdb.execute("jtree $1")
except Exception: exit(1)
try: gdb.execute("jtree $1 v3Global.m_rootp")
except Exception: exit(1)
end
quit 0
