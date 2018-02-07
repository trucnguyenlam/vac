//
// Created by esteffin on 25/04/17.
//

#ifndef VACSAT_SMT_PRUNING_H
#define VACSAT_SMT_PRUNING_H

#include <memory>
#include <vector>
#include "SMT.h"
#include "Logics.h"
#include "Policy.h"

/** @file file containing function and class definition for the pruning of policies */

namespace SMT {

    struct atom_status {
    public:
        enum status {
            UNKNOWN,
            USED,
            UNUSED
        };

        static std::vector<std::shared_ptr<atom_status>> create(std::shared_ptr<arbac_policy>& policy) {
            std::vector<std::shared_ptr<atom_status>> result((ulong) policy->atom_count());
            for (auto &&atom : policy->atoms()) {
                int size = (int) pow(2, atom->bv_size);
                result[atom->role_array_index] = std::shared_ptr<atom_status>(new atom_status(size, atom->to_string()));
            }

            return result;
        }

        inline status get_status(int value) {
            if (invalid) {
                log->error("atom_status object in cache is invalid");
                throw std::runtime_error("Object in cache is invalid");
            }
            return statuses[value];
        }

        void set_unused() {
            if (invalid) {
                log->error("atom_status object in cache is invalid");
                throw std::runtime_error("Object in cache is invalid");
            }
            for (int i = 0; i < values_count; ++i) {
                statuses[i] = UNUSED;
            }
        }

        inline void set_value(int value, status _status) {
            if (invalid) {
                log->error("atom_status object in cache is invalid");
                throw std::runtime_error("Object in cache is invalid");
            }
            statuses[value] = _status;
        }

        std::string to_string() const {
            std::stringstream fmt;
            fmt << name << ":" << std::endl;
            for (int i = 0; i < statuses.size(); ++i) {
                fmt << "\t" << i << ": " << status_to_string(statuses[i]) << std::endl;
            }
            return fmt.str();
        }

        friend std::ostream& operator<<(std::ostream& stream, const atom_status& self) {
            stream << self.to_string();
            return stream;
        }

    private:
        atom_status() : invalid(true), values_count(0), name("") { }
        atom_status(int _values_count, std::string _name) :
                invalid(false),
                values_count(_values_count),
                statuses((ulong) _values_count),
                name(_name) {
            for (int i = 0; i < _values_count; ++i) {
                statuses[i] = UNKNOWN;
            }
        }
        static inline const std::string status_to_string(status _status) {
            switch (_status) {
                case UNKNOWN:
                    return "UNKNOWN";
                case USED:
                    return "USED";
                case UNUSED:
                    return "UNUSED";
            }
            return "err";
        }
        const bool invalid = true;
        const int values_count;
        std::vector<status> statuses;
        const std::string name;
    };

    template <typename TVar, typename TExpr>
    bool apply_infini_admin(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                            const std::shared_ptr<arbac_policy>& policy,
                            const Expr& query,
                            const std::vector<std::shared_ptr<atom_status>>& atom_statuses,
                            int steps,
                            int rounds,
                            int wanted_threads_count);

    /** @fn function that returns true if the target expression is not reachable
     * @param solver a pointer to the SMT solver
     * @param policy a pointer to the policy to be used
     * @param to_check the Expr to be checked
     * @param free a set of Expr that will be considered free (used for tampone)
     * @param excluded_rules a list of rulep to be excluded from the encoding
     * @param tracked_user (optional) the user to be tracked
     * */
    template <typename TVar, typename TExpr>
    bool apply_r6(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                  const std::shared_ptr<arbac_policy>& policy,
                  const Expr& to_check,
                  const std::set<Expr>& free,
                  const std::list<rulep>& excluded_rules,
                  const userp& tracked_user = nullptr);

    /** @fn function that returns true if the target expression is not reachable
     * @param solver a pointer to the SMT solver
     * @param policy a pointer to the policy to be used
     * @param to_check the Expr to be checked
     * @param free a set of Expr that will be considered free (used for tampone)
     * @param excluded_rules a rulep to be excluded from the encoding
     * @param tracked_user (optional) the user to be tracked
     * */
    template <typename TVar, typename TExpr>
    bool apply_r6(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                  const std::shared_ptr<arbac_policy>& policy,
                  const Expr& to_check,
                  const std::set<Expr>& free,
                  const rulep& excluded_rule,
                  const userp& tracked_user = nullptr);

    template <typename TVar, typename TExpr>
    void prune_policy(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                      const std::shared_ptr<arbac_policy>& policy);

}


#endif //VACSAT_SMT_PRUNING_H