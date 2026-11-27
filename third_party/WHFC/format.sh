find . -iname "*.h" -o -iname "*.cpp" -o -iname "*.cc" -o -iname "*.hpp" | xargs clang-format -i --Wno-error=unknown
