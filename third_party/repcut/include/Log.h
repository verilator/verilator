// Logger: fprintf to stderr, gated by ctx_level.  Errors always print.

#pragma once

#include "repcut.h"

#include <cstdarg>
#include <cstdio>

namespace repcut {

    inline bool rcp_should_log(RepCutLogLevel ctx_level, RepCutLogLevel level)
    {
        if (level == REPCUT_LOG_ERROR)
            return true;
        return static_cast<int>(level) <= static_cast<int>(ctx_level);
    }

    inline void rcp_log(RepCutLogLevel ctx_level, RepCutLogLevel level, const char* fmt, ...)
    {
        if (!rcp_should_log(ctx_level, level))
            return;
        va_list ap;
        va_start(ap, fmt);
        std::vfprintf(stderr, fmt, ap);
        va_end(ap);
    }

} // namespace repcut