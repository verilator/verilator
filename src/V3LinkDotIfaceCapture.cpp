
#include "V3LinkDotIfaceCapture.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3Global.h"
#include "V3SymTable.h"

#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace LinkDotIfaceCapture {

const bool kDefaultEnabled = true;

using CapturedMap
    = std::unordered_map<const AstRefDType*, LinkDotIfaceCapture::CapturedIfaceTypedef>;

static CapturedMap s_map;
static bool s_enabled = kDefaultEnabled;

CapturedMap& capturedMap() { return s_map; }
bool& captureEnabled() { return s_enabled; }

void enable(bool flag) {
    captureEnabled() = flag;
    if (!flag) capturedMap().clear();
}

bool enabled() { return captureEnabled(); }

void reset() { capturedMap().clear(); }

void add(AstRefDType* refp, AstCell* cellp, AstNodeModule* ownerModp, VSymEnt* ownerSymp,
         AstTypedef* typedefp) {
    if (!refp) return;
    capturedMap()[refp] = CapturedIfaceTypedef{refp, cellp, ownerModp, ownerSymp, typedefp ? typedefp : refp->typedefp()};
}

void add(const CapturedIfaceTypedef& entry) {
    if (!entry.refp) return;
    capturedMap()[entry.refp] = entry;
}

bool contains(const AstRefDType* refp) {
    if (!refp) return false;
    return capturedMap().find(refp) != capturedMap().end();
}

const CapturedIfaceTypedef* find(const AstRefDType* refp) {
    if (!refp) return nullptr;
    const auto it = capturedMap().find(refp);
    if (VL_UNLIKELY(it == capturedMap().end())) return nullptr;
    return &it->second;
}

void forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn) {
    if (!fn) return;
    for (const auto& entry : capturedMap()) fn(entry.second);
}

bool replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp) {
    if (!oldRefp || !newRefp) return false;
    auto& map = capturedMap();
    const auto it = map.find(oldRefp);
    if (it == map.end()) return false;
    auto entry = it->second;
    entry.refp = newRefp;
    map.erase(it);
    map.emplace(newRefp, entry);
    return true;
}

bool replaceTypedef(const AstTypedef* oldTypedefp, AstTypedef* newTypedefp) {
    if (!oldTypedefp || !newTypedefp) return false;
    auto& map = capturedMap();
    for (auto& entry : map) {
        if (entry.second.typedefp == oldTypedefp) {
            entry.second.typedefp = newTypedefp;
            return true;
        }
    }
    return false;
}

std::size_t size() { return capturedMap().size(); }

void propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp) {
    if (!origRefp || !newRefp) return;
    const CapturedIfaceTypedef* const entry = find(origRefp);
    if (!entry) return;
    AstTypedef* const origTypedefp = entry->typedefp ? entry->typedefp : origRefp->typedefp();
    AstTypedef* const clonedTypedefp = origTypedefp ? origTypedefp->clonep() : nullptr;
    if (entry->cellp) newRefp->user2p(entry->cellp);
    newRefp->user3(false);
    if (clonedTypedefp) {
        newRefp->typedefp(clonedTypedefp);
        UINFO(2, "[iface-debug] rebound typedef ref=" << origRefp << " clone=" << newRefp << " typedefp=" << origTypedefp << " typedefClone=" << clonedTypedefp);
    } else if (origTypedefp) {
        UINFO(1, "[iface-debug] missing typedef clone ref=" << origRefp << " typedefp=" << origTypedefp << " ownerMod=" << (entry->ownerModp ? entry->ownerModp->name() : "<null>"));
    }
    UINFO(2, "[iface-debug] scrub typedef" << " ownerMod=" << (entry->ownerModp ? entry->ownerModp->name() : "<null>") << " ref=" << origRefp << " clone=" << newRefp << " cell=" << entry->cellp);
    replaceRef(origRefp, newRefp);
    UINFO(3, "[iface-debug] scrubbed typedef name=" << newRefp->name() << " orig=" << origRefp << " clone=" << newRefp << " user2=" << newRefp->user2p() << " user3=" << newRefp->user3() << " typedefp=" << newRefp->typedefp());
}

void dumpCaptured(int uinfoLevel) {
    UINFO(uinfoLevel, "[iface-debug] dump captured typedefs count=" << capturedMap().size() << " enabled=" << enabled());
    for (const auto& kv : capturedMap()) {
        const CapturedIfaceTypedef& entry = kv.second;
        UINFO(uinfoLevel, "  entry refp=" << entry.refp << " name=" << (entry.refp ? entry.refp->name() : "") << " cell=" << entry.cellp << " ownerMod=" << entry.ownerModp << " typedefp=" << entry.typedefp << " user2=" << (entry.refp ? entry.refp->user2p() : nullptr) << " user3=" << (entry.refp ? entry.refp->user3() : false));
    }
}

}  // namespace LinkDotIfaceCapture
