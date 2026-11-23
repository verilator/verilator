#pragma once

#include <atomic>
#include <tbb/enumerable_thread_specific.h>
#include <tbb/scalable_allocator.h>
#include <vector>

namespace whfc {

    template<typename T>
    class BufferedVector {
    public:
        using vec_t = std::vector<T, tbb::scalable_allocator<T>>;

        BufferedVector(size_t max_size) :
            data(max_size, T()), buffers([&] {
                vec_t x;
                x.reserve(MAX_BUFFER_SIZE);
                return x;
            }) {}

        void clear() {
            back.store(0, std::memory_order_relaxed);
            assert(std::all_of(buffers.begin(), buffers.end(), [&](vec_t& x) { return x.empty(); }));
        }

        size_t size() const { return back.load(std::memory_order_relaxed); }

        bool empty() const { return size() == 0; }

        size_t capacity() const { return data.size(); }

        void adapt_capacity(size_t sz) {
            if (sz > data.size()) {
                data.resize(sz, T());
            }
        }

        void push_back_atomic(const T& element) {
            size_t pos = back.fetch_add(1, std::memory_order_relaxed);
            assert(pos < data.size());
            data[pos] = element;
        }

        void push_back_buffered(const T& element) { local_buffer().push_back(element); }

        void finalize() {
            for (vec_t& buffer : buffers) {
                BufferHandle({ buffer, data, back }).flush_buffer();
            }
        }

        void swap_container(vec_t& o) {
            if (o.size() < data.size()) {
                o.resize(data.size());
            }
            std::swap(o, data);
        }

        void set_size(size_t s) { back.store(s, std::memory_order_relaxed); }

        auto begin() { return data.begin(); }
        auto end() { return data.begin() + size(); }
        T& operator[](size_t pos) { return data[pos]; }
        const T& operator[](size_t pos) const { return data[pos]; }

        struct BufferHandle {
            vec_t& buffer;
            vec_t& data;
            std::atomic<size_t>& back;

            void flush_buffer() {
                if (!buffer.empty()) {
                    size_t pos = back.fetch_add(buffer.size(), std::memory_order_relaxed);
                    assert(pos + buffer.size() - 1 < data.size());
                    std::copy_n(buffer.begin(), buffer.size(), data.begin() + pos);
                    buffer.clear();
                }
            }

            void push_back(const T& element) {
                buffer.push_back(element);
                if (buffer.size() == MAX_BUFFER_SIZE) {
                    flush_buffer();
                }
            }
        };
        BufferHandle local_buffer() { return { buffers.local(), data, back }; }


        struct RandomAccessRange {
            size_t actual_size;
            const vec_t& data_ref;
            const T& operator[](size_t i) const { return data_ref[i]; }
            size_t size() const { return actual_size; }
        };
        RandomAccessRange range() const { return { size(), data }; }

        const vec_t& getData() const { return data; }

    private:
        vec_t data;
        std::atomic<size_t> back{ 0 };
        tbb::enumerable_thread_specific<vec_t> buffers;
        static constexpr size_t MAX_BUFFER_SIZE = 1024;
    };

} // namespace whfc
