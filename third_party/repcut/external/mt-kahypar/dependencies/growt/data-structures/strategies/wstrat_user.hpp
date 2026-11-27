/*******************************************************************************
 * data-structures/strategy/wstrat_user.h
 *
 * see below
 *
 * Part of Project growt - https://github.com/TooBiased/growt.git
 *
 * Copyright (C) 2015-2016 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#pragma once

#include <atomic>
#include <cstddef>
#include <string>

/*******************************************************************************
 *
 * This is a worker strategy for our growtable.
 *
 * Every worker strategy has to implement the following
 *  - subclass: global_data_t      (is stored at the growtable object)
 *  - subclass: local_data_t       (is stored at each handle)
 *     - init(...)
 *     - deinit()
 *     - execute_migration(...)
 *
 * This specific strategy uses user-threads for the migration.
 * Whenever the table is growing, all new operations help migrating the
 * old table, before the operation is executed. This is a very simple
 * technique therefore, nothing has to be saved/initialized
 *
 ******************************************************************************/

namespace growt
{

template <class Parent> class wstrat_user
{
  public:
    // The enslavement strategy, does not actually need any global data
    class global_data_type
    {
      public:
        global_data_type() {}
        global_data_type(const global_data_type& source) = delete;
        global_data_type& operator=(const global_data_type& source) = delete;
        ~global_data_type()                                         = default;
    };


    // No initialization or deinitialization needed.
    class local_data_type
    {
      public:
        local_data_type(Parent& parent) : _parent(parent) {}
        local_data_type(const local_data_type& source) = delete;
        local_data_type& operator=(const local_data_type& source) = delete;
        local_data_type(local_data_type&& source)                 = default;
        local_data_type& operator=(local_data_type&& source) = default;
        ~local_data_type()                                   = default;

        Parent& _parent;

        template <class EStrat> inline void init(EStrat&) {}
        inline void                         deinit() {}

        template <class ESLocal>
        inline void execute_migration(ESLocal& estrat, size_t)
        {
            estrat.migrate();
        }
    };

    static std::string name() { return "w_user"; }
};

} // namespace growt
