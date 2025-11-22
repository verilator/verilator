#ifndef VERILATOR_V3LINKDOTIFACECAPTURE_H_
#define VERILATOR_V3LINKDOTIFACECAPTURE_H_

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
    AstNodeModule* ownerModp = nullptr;        // Module where the RefDType lives
    VSymEnt* ownerSymp = nullptr;
    AstTypedef* typedefp = nullptr;            // Typedef definition being referenced
    AstNodeModule* typedefOwnerModp = nullptr;  // Interface/module that owns typedefp
    AstRefDType* pendingClonep = nullptr;       // Cloned RefDType awaiting typedef rebinding
};

void enable(bool flag);
bool enabled();

void reset();
void add(AstRefDType* refp, AstCell* cellp, AstNodeModule* ownerModp, VSymEnt* ownerSymp,
         AstTypedef* typedefp = nullptr, AstNodeModule* typedefOwnerModp = nullptr);
void add(const CapturedIfaceTypedef& entry);
bool contains(const AstRefDType* refp);
const CapturedIfaceTypedef* find(const AstRefDType* refp);
void forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn);
bool replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp);
bool replaceTypedef(const AstRefDType* refp, AstTypedef* newTypedefp);
std::size_t size();

void propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp);
void dumpCaptured(int uinfoLevel = 3);

}  // namespace LinkDotIfaceCapture

#endif  // VERILATOR_V3LINKDOTIFACECAPTURE_H_
