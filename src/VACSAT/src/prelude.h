
//
// Created by esteffin on 05/05/17.
//

#ifndef VACSAT_PRELUDE_H
#define VACSAT_PRELUDE_H

#include <set>

template <typename T>
static inline bool contains(const std::set<T>& set, const T& elem) {
    return set.find(elem) != set.end();
}

template<class InputIterator, class T>
static inline bool contains(InputIterator first, InputIterator last, const T& val) {
    return std::find(first, last, val) != last;
}

#endif //VACSAT_PRELUDE_H
