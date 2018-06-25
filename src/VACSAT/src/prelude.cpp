//
// Created by esteffin on 3/28/18.
//
#include "prelude.h"

namespace SMT {

    unexpected_error::unexpected_error(std::string msg) :
            what_message(std::move(msg)),
            file_name(nullptr),
            line_number(-1),
            function(nullptr),
            pretty_function(nullptr) { }

    unexpected_error::unexpected_error(std::string msg, const char* file, const int line) :
            what_message(std::move(msg)),
            file_name(file),
            line_number(line),
            function(nullptr),
            pretty_function(nullptr) {
        std::stringstream stream;
        stream << what_message << std::endl;
        if (file_name != nullptr) {
            stream << "\t@ " << file_name << ": " << line_number;
        }
        what_message = stream.str();
    }

    unexpected_error::unexpected_error(std::string msg,
                                       const char* file,
                                       const int line,
                                       const char* _function,
                                       const char* _pretty_function) :
            what_message(std::move(msg)),
            file_name(file),
            line_number(line),
            function(_function),
            pretty_function(_pretty_function) {
        std::stringstream stream;
        stream << what_message << std::endl;
        if (file_name != nullptr) {
            stream << "\t@ " << file_name << ": " << line_number << std::endl;
        }
        if (function != nullptr) {
            stream << "\tin function: " << function << std::endl;
        }
        if (pretty_function != nullptr) {
            stream << "\tprettied: " << pretty_function << std::endl;
        }
        what_message = stream.str();
    }

    //    __PRETTY_FUNCTION__
    const char* unexpected_error::what() const noexcept {
        return what_message.c_str();
    }


    const std::string maybe_bool_to_string(const maybe_bool info) {
        switch (info) {
            case maybe_bool::UNKNOWN:
                return "UNKNOWN";
            case maybe_bool::YES:
                return "YES";
            case maybe_bool::NO:
                return "NO";
        }
        return "uh?";
    }

    const std::string get_timestamp(bool millisecond) {
        std::stringstream fmt;
        if (!millisecond) {
            auto t = std::time(nullptr);
            auto tm = *std::localtime(&t);
            fmt << std::put_time(&tm, "%H:%M:%S %d-%m-%Y");
            return fmt.str();
        }

        using namespace std::chrono;

        // get current time
        auto now = system_clock::now();

        // get number of milliseconds for the current second
        // (remainder after division into seconds)
        auto ms = duration_cast<milliseconds>(now.time_since_epoch()) % 1000;

        // convert to std::time_t in order to convert to std::tm (broken time)
        auto timer = system_clock::to_time_t(now);

        // convert to broken time
        std::tm bt = *std::localtime(&timer);

        auto t = std::time(nullptr);
        fmt << std::put_time(&bt, "%H:%M:%S");
        fmt << '.' << std::setfill('0') << std::setw(3) << ms.count();
        fmt << std::put_time(&bt, " %d-%m-%Y");
        return fmt.str();
    }

    const std::string bool_to_true_false(bool b) {
        return b ? "true" : "false";
    }

    const std::string str_to_lower(const std::string &str) {
        std::string res = "";
        for (auto &&ch : str) {
            res += std::tolower(ch);
        }
        return res;
    }

}