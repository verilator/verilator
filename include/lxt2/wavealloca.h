/*
 * Copyright (c) Tony Bybell 1999.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 */

#ifndef WAVE_ALLOCA_H
#define WAVE_ALLOCA_H
#include <stdlib.h>
#ifdef HAVE_ALLOCA_H
#include <alloca.h>
#elif defined(__GNUC__)
#ifndef __MINGW32__
#ifndef alloca
#define alloca __builtin_alloca
#endif
#else
#include <malloc.h>
#endif
#elif defined(_MSC_VER)
#include <malloc.h>
#define alloca _alloca
#endif
#define wave_alloca alloca
#endif

