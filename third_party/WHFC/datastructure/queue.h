#pragma once

#include <vector>
#include "../util/range.h"

template<typename T>
class LayeredQueue {
private:
    std::vector<T> queue;

public:
    size_t layerfront = 0, layerend = 0, qfront = 0;
    explicit LayeredQueue(const size_t num_elements = 0) { reserve(num_elements); }
    // Note. Use reinitialize() if you want to keep entries in the underlying vector intact, and ensure these won't be pushed again
    void reinitialize(size_t x) {
        layerfront = x;
        layerend = x;
        qfront = x;
        queue.erase(queue.begin() + x, queue.end());
    }
    void reserve(size_t sz) { queue.reserve(sz); }
    void reinitialize() { reinitialize(queueEnd()); }
    void clear() {
        layerfront = 0;
        layerend = 0;
        qfront = 0;
        queue.clear();
    }
    bool empty() const { return qfront == queueEnd(); }
    bool currentLayerEmpty() const { return qfront == layerend; }
    T pop() { return queue[qfront++]; }
    T previousLayerPop() { return queue[layerfront++]; }
    void finishNextLayer() { layerend = queueEnd(); }
    void push(const T x) { queue.push_back(x); }
    bool previousLayerEmpty() const { return layerfront == layerend; }
    T capacity() const { return static_cast<T>(queue.size()); }
    std::vector<T>& data() { return queue; }
    template<typename Func>
    void forAllEverContainedElements(Func f) {
        for (size_t i = 0; i < queueEnd(); i++) {
            f(queue[i]);
        }
    }
    const_range<std::vector<T>> range(size_t __begin, size_t __end) { return { queue.begin() + __begin, queue.cbegin() + __end }; }
    const_range<std::vector<T>> currentLayer() { return range(qfront, layerend); }
    const_range<std::vector<T>> allElements() { return range(0, queueEnd()); }
    size_t queueEnd() const { return queue.size(); }
    size_t size() const { return queue.size() - qfront; }
    T popBack() {
        T back = queue.back();
        queue.pop_back();
        return back;
    }

    T elementAt(const size_t pos) const { return queue[pos]; }
    void setTo(const size_t pos, T element) { queue[pos] = element; }

    T swapFrontToPositionAndPop(size_t pos) {
        std::swap(queue[pos], queue[qfront]);
        return pop();
    }

    template<typename URBG>
    void shuffleQueue(URBG& urbg, size_t a, size_t b) {
        std::shuffle(queue.begin() + a, queue.begin() + b, urbg);
    }

    template<typename URBG>
    void shuffleQueue(URBG& urbg) {
        shuffleQueue(urbg, qfront, queueEnd());
    }

    template<typename URBG>
    void shuffleCurrentLayer(URBG& urbg) {
        shuffleQueue(urbg, qfront, layerend);
    }
};
