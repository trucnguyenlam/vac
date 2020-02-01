
//
// Created by esteffin on 05/05/17.
//

#ifndef VACSAT_PRELUDE_H
#define VACSAT_PRELUDE_H

#include <vector>
#include <list>
#include <set>
#include <algorithm>
#include "config.h"

namespace SMT {

typedef unsigned long long int ulong64;

class unexpected_error : public std::exception
{
    std::string what_message;
public:
    unexpected_error(std::string msg) : what_message(msg) {
    }
    const char* what() const noexcept override {
        return what_message.c_str();
    }
};

template <typename T, typename TCmp=std::less<T>>
std::set<T, TCmp> setUnion(const std::set<T, TCmp>& a, const std::set<T, TCmp>& b) {
    std::set<T, TCmp> result = a;
    result.insert(b.begin(), b.end());
    return result;
}

template <typename T>
static inline bool contains(const std::set<T> &set, const T &elem) {
    return set.find(elem) != set.end();
}

template <template <typename> typename TCollection, typename TVal>
static inline bool contains(const TCollection<TVal>& collection, const TVal &elem) {
    static_assert(std::is_base_of<std::vector<TVal>, TCollection<TVal>>::value ||
                  std::is_base_of<std::list<TVal>, TCollection<TVal>>::value,
                  "TCollection<TVar> is not derived from either vector and list");

    for (auto &&value :collection) {
        if (value == elem) {
            return true;
        }
    }
    return false;
};

//    template <typename T, typename TCmp>
//    static inline bool contains_ptr(const std::set<std::weak_ptr<T>, TCmp> &set, const std::shared_ptr<T> &elem) {
//        return set.find(elem) != set.end();
//    }
//
//    template <typename T>
//    static inline bool contains_ptr(const std::set<std::shared_ptr<T>> &set, const std::weak_ptr<T> &elem) {
//        return set.find(elem.lock()) != set.end();
//    }


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

template <typename TVal, typename TComparer>
void print_collection(const std::set<std::shared_ptr<TVal>, TComparer>& set, std::string prefix = "", spdlog::level::level_enum lvl = spdlog::level::info) {
//        typedef std::shared_ptr<TVal> TValp;
//        static_assert(std::is_base_of<std::vector<TValp>, TCollection<TValp, TComparer>>::value ||
//                      std::is_base_of<std::list<TValp>, TCollection<TValp, TComparer>>::value   ||
//                      std::is_base_of<std::set<TValp, TComparer>, TCollection<TValp, TComparer>>::value,
//                      "TCollection<TVar> is not derived from either vector, list and set");

    for (auto &&valuep :set) {
        log->log(lvl, "{}{}", prefix, *valuep);
    }
};

template <template <typename> typename TCollection, typename TVal>
void print_collection(const TCollection<std::shared_ptr<TVal>>& collection, std::string prefix = "", spdlog::level::level_enum lvl = spdlog::level::info) {
    typedef std::shared_ptr<TVal> TValp;
    static_assert(std::is_base_of<std::vector<TValp>, TCollection<TValp>>::value ||
                  std::is_base_of<std::list<TValp>, TCollection<TValp>>::value   ||
                  std::is_base_of<std::set<TValp>, TCollection<TValp>>::value,
                  "TCollection<TVar> is not derived from either vector, list and set");

    for (auto &&valuep :collection) {
        log->log(lvl, "{}{}", prefix, *valuep);
    }
};

static int bits_count(int pc) {
    int i = 1, bit = 0;

    if (pc < 2 ) return 1;

    while (pc >= i) {
        i = i * 2;
        bit++;
    }

    return (bit);
}

template <template <typename> typename TCollection, typename TVal>
static inline TCollection<std::shared_ptr<TVal>> lock_collection(const TCollection<std::weak_ptr<TVal>>& collection) {
    static_assert(std::is_base_of<std::vector<TVal>, TCollection<TVal>>::value ||
                  std::is_base_of<std::list<TVal>, TCollection<TVal>>::value,
                  "TCollection<TVar> is not derived from either vector and list");
    TCollection<std::shared_ptr<TVal>> res;
    for (auto &&item :collection) {
        res.push_back(item.lock());
    }
    return res;
};

template <typename TVal>
static inline std::set<std::shared_ptr<TVal>> lock_collection(const std::set<std::weak_ptr<TVal>>& collection) {
    std::set<std::shared_ptr<TVal>> res;
    for (auto &&item :collection) {
        res.insert(item.lock());
    }
    return res;
};
}

#endif //VACSAT_PRELUDE_H
