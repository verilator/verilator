#ifndef VERILATOR_V3LINKDOTIFACECAPTURE_H_
#define VERILATOR_V3LINKDOTIFACECAPTURE_H_

/*
LinkDotIfaceCapture: it stores (refp, typedefp, cellp, owners, pendingClone), plus helpers for add/find/replace/forEach/erase.

Functions are used by either param cloning (replaceRef/replaceTypedef/propagateClone) or LinkDot (contains/find/getCapturedTypedef/erase).

The capture lifecycle in V3LinkDot.cpp now has a single path: capture when we see an interface typedef, rebind from capturedTypedefp if symbol lookup fails, then retire the entry.

V3Param.cpp only touches the capture map inside the module clone scrub. That code now just rebinds typedefs and propagates clones—no special cases.
*/


#include "config_build.h"

#include <functional>
#include <cstddef>

class AstCell;
class AstNodeModule;
class AstRefDType;
class AstTypedef;
class VSymEnt;

namespace LinkDotIfaceCapture {

struct CapturedIfaceTypedef final {
    AstRefDType* refp = nullptr;
    AstCell* cellp = nullptr;
    // Module where the RefDType lives
    AstNodeModule* ownerModp = nullptr;
    VSymEnt* ownerSymp = nullptr;
    // Typedef definition being referenced
    AstTypedef* typedefp = nullptr;
    // Interface/module that owns typedefp
    AstNodeModule* typedefOwnerModp = nullptr;
    // Cloned RefDType awaiting typedef rebinding
    AstRefDType* pendingClonep = nullptr;
};

void enable(bool flag);
bool enabled();

void reset();
void add(AstRefDType* refp, AstCell* cellp, AstNodeModule* ownerModp, VSymEnt* ownerSymp,
         AstTypedef* typedefp = nullptr, AstNodeModule* typedefOwnerModp = nullptr);
void add(const CapturedIfaceTypedef& entry);
bool contains(const AstRefDType* refp);
const CapturedIfaceTypedef* find(const AstRefDType* refp);
AstTypedef* getCapturedTypedef(const AstRefDType* refp);
void forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn);
bool replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp);
bool replaceTypedef(const AstRefDType* refp, AstTypedef* newTypedefp);
bool erase(const AstRefDType* refp);
std::size_t size();

void propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp);
void dumpCaptured(int uinfoLevel = 3);


}  // namespace LinkDotIfaceCapture

#endif  // VERILATOR_V3LINKDOTIFACECAPTURE_H_
