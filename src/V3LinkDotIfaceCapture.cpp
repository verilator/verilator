
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

static AstNodeModule* findOwnerModule(AstNode* nodep) {
    for (AstNode* curp = nodep; curp; curp = curp->backp()) {
        if (AstNodeModule* const modp = VN_CAST(curp, NodeModule)) return modp;
    }
    return nullptr;
}

void enable(bool flag) {
    captureEnabled() = flag;
    if (!flag) capturedMap().clear();
}

bool enabled() { return captureEnabled(); }

void reset() { capturedMap().clear(); }

void add(AstRefDType* refp, AstCell* cellp, AstNodeModule* ownerModp, VSymEnt* ownerSymp,
         AstTypedef* typedefp, AstNodeModule* typedefOwnerModp) {
    if (!refp) return;
    AstTypedef* const resolvedTypedefp = typedefp ? typedefp : refp->typedefp();
    AstNodeModule* resolvedTypedefOwner = typedefOwnerModp;
    if (!resolvedTypedefOwner && resolvedTypedefp)
        resolvedTypedefOwner = findOwnerModule(resolvedTypedefp);
    capturedMap()[refp] = CapturedIfaceTypedef{refp,cellp, ownerModp, ownerSymp, resolvedTypedefp, resolvedTypedefOwner, nullptr};
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

AstTypedef* getCapturedTypedef(const AstRefDType* refp) {
    if (const CapturedIfaceTypedef* const entry = find(refp)) return entry->typedefp;
    return nullptr;
}

void forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn) {
    if (!fn) return;
    auto& map = capturedMap();
    std::vector<const AstRefDType*> keys;
    keys.reserve(map.size());
    for (const auto& kv : map) keys.push_back(kv.first);

    for (const AstRefDType* key : keys) {
        const auto it = map.find(key);
        if (it == map.end()) continue;  // entry may have been erased
        CapturedIfaceTypedef& entry = it->second;
        if (entry.cellp && entry.refp && entry.refp->user2p() != entry.cellp) {
            entry.refp->user2p(entry.cellp);
        }
        fn(entry);
    }
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

static bool finalizeCapturedEntry(CapturedMap::iterator it, const char* reasonp) {
    CapturedIfaceTypedef& entry = it->second;
    AstRefDType* const pendingRefp = entry.pendingClonep;
    AstTypedef* const reboundTypedefp = entry.typedefp;
    if (!pendingRefp || !reboundTypedefp) return false;
    AstRefDType* const origRefp = entry.refp;
    if (entry.cellp) pendingRefp->user2p(entry.cellp);
    pendingRefp->user3(false);
    pendingRefp->typedefp(reboundTypedefp);
    entry.pendingClonep = nullptr;
    return true;
}

bool replaceTypedef(const AstRefDType* refp, AstTypedef* newTypedefp) {
    if (!refp || !newTypedefp) return false;
    auto& map = capturedMap();
    auto it = map.find(refp);
    if (it == map.end()) return false;
    it->second.typedefp = newTypedefp;
    it->second.typedefOwnerModp = findOwnerModule(newTypedefp);
    if (finalizeCapturedEntry(it, "typedef clone")) return true;
    return true;
}

bool erase(const AstRefDType* refp) {
    if (!refp) return false;
    auto& map = capturedMap();
    const auto it = map.find(refp);
    if (it == map.end()) return false;
    map.erase(it);
    return true;
}

std::size_t size() { return capturedMap().size(); }

void propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp) {
    if (!origRefp || !newRefp) return;
    auto& map = capturedMap();
    auto it = map.find(origRefp);
    if (it == map.end()) {
        const string msg = string{"iface capture propagateClone missing entry for orig="} + cvtToStr(origRefp);
        v3fatalSrc(msg);
    }
    CapturedIfaceTypedef& entry = it->second;

    if (entry.cellp) newRefp->user2p(entry.cellp);
    newRefp->user3(false);
    entry.pendingClonep = newRefp;

    if (finalizeCapturedEntry(it, "ref clone")) return;
}

}  // namespace LinkDotIfaceCapture
