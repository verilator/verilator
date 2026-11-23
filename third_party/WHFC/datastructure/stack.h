#pragma once

#include <vector>

template<typename T>
class FixedCapacityStack {
private:
    std::vector<T> stack;

public:
    explicit FixedCapacityStack(const size_t num_elements = 0) { stack.reserve(num_elements); }
    void reserve(size_t sz) { stack.reserve(sz); }
    void clear() { stack.clear(); }
    bool empty() const { return stack.empty(); }
    void popDownTo(const size_t x) {
        assert(size() >= x + 1);
        stack.erase(stack.begin() + x + 1, stack.end());
    }
    T pop() {
        assert(!empty());
        T res = top();
        stack.pop_back();
        return res;
    }
    const T& top() const {
        assert(!empty());
        return stack.back();
    }
    void push(const T& x) { stack.push_back(x); }
    const T& at(const size_t t) const { return stack[t]; }
    size_t size() const { return stack.size(); }
    size_t capacity() const { return stack.capacity(); }
    std::vector<T>& data() { return stack; }
};
