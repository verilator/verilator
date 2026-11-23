/*******************************************************************************
 * data-structures/returnelement.h
 *
 * Some definitions that are important as function return values.
 *
 * Part of Project growt - https://github.com/TooBiased/growt.git
 *
 * Copyright (C) 2015-2016 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#pragma once

#include <stdlib.h>
#include <tuple>

namespace growt
{

enum class ReturnCode
{
    // bit pattern:  1 = success ;   2 = not found key ;   4 = found key
    //               8 = insert  ;  16 = update        ;  32 = delete
    //              64 = full    ; 128 = invalid cell  ; 256 = backoff
    //            1024 = TSX

    ERROR = 0,

    SUCCESS_IN  = 9,  // success+insert
    SUCCESS_UP  = 17, // success+update
    SUCCESS_DEL = 33, // success+delete

    UNSUCCESS_NOT_FOUND    = 2,
    UNSUCCESS_ALREADY_USED = 4,
    UNSUCCESS_FULL         = 64,
    UNSUCCESS_INVALID      = 128,
    UNSUCCESS_BACKOFF      = 256,

    TSX_SUCCESS_IN  = 1033, // success+insert+TSX
    TSX_SUCCESS_UP  = 1041, // success+update+TSX
    TSX_SUCCESS_DEL = 1057, // success+delete+TSX

    TSX_UNSUCCESS_NOT_FOUND    = 1026, // not found   +TSX
    TSX_UNSUCCESS_ALREADY_USED = 1028, // already used+TSX
    TSX_UNSUCCESS_FULL         = 1088, // full        +TSX
    TSX_UNSUCCESS_INVALID      = 1152, // invalid     +TSX

    TSX_ABORT = 1024 // TSX+ERROR
};

inline bool successful(ReturnCode ec) { return (static_cast<unsigned int>(ec) & 1u); }


// class ReturnElement
// {
// public:
//     using Key  = uint64_t;
//     using Data = uint64_t;

//     ReturnElement() : first(0), second(0) { }
//     ReturnElement(Key k, Data d) : first(k), second(d) { }

//     static ReturnElement getEmpty() { return ReturnElement( 0, 0 ); }

//     Key  first;
//     Data second;

//     bool isValid()  const { return first != 0; }

//     operator bool() const
//     {   return first != 0;   }
//     operator std::tuple<Key&, Data&> ()
//     {   return std::tuple<Key&, Data&>{ first, second };   }

// private:
// };

} // namespace growt
