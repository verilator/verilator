
#include "V3LinkDotIfaceCapture.h"

#include "V3Ast.h"
#include "V3SymTable.h"

#include <unordered_map>

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

void add(AstRefDType* refp, AstCell* cellp, VSymEnt* ownerSymp) {
    if (!refp) return;
    capturedMap()[refp] = CapturedIfaceTypedef{refp, cellp, ownerSymp};
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

std::size_t size() { return capturedMap().size(); }

void propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp) {
    if (!origRefp || !newRefp) return;
    const CapturedIfaceTypedef* const entry = find(origRefp);
    if (!entry) return;
    if (entry->cellp) newRefp->user2p(entry->cellp);
    replaceRef(origRefp, newRefp);
}

}  // namespace LinkDotIfaceCapture
