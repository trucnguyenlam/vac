
//
// Created by esteffin on 05/05/17.
//

#ifndef VACSAT_PRELUDE_H
#define VACSAT_PRELUDE_H

#include <set>
#include <algorithm>
#include "debug.h"

namespace SMT {

    template <typename T>
    static inline bool contains(const std::set<T> &set, const T &elem) {
        return set.find(elem) != set.end();
    }

    template <class InputIterator, class T>
    static inline bool contains(InputIterator first, InputIterator last, const T &val) {
        return std::find(first, last, val) != last;
    }

//    static inline void str_to_lower(std::string &str) {
//        std::transform(str.begin(), str.end(), str.begin(), ::tolower);
//    }

    static inline std::string str_to_lower(const std::string &str) {
        std::string res = "";
        for (auto &&ch : str) {
            res += std::tolower(ch);
        }
        return res;
    }

    template<typename _InputIterator, typename _Predicate>
    bool iterable_exists(_InputIterator first, _InputIterator last, _Predicate p) {
        return std::find_if(first, last, p) != last;
    };
}

#endif //VACSAT_PRELUDE_H
