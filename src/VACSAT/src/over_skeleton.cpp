//
// Created by esteffin on 12/5/17.
//

#include "over_skeleton.h"
#include "prelude.h"

namespace SMT {

    class simple_role_choicer: public role_choicer {

        const std::shared_ptr<arbac_policy>& policy;

    public:
        explicit simple_role_choicer(const std::shared_ptr<arbac_policy>& _policy) :
                policy(_policy) { }

        Choice classify(atomp r) const override {
//            if (r->name == "r1" || r->name == "r2") {
//                return REQUIRED;
//            }
            return FREE;
        }
        int get_required_count() const override {
            int count = 0;
            for (auto &&atom :policy->atoms()) {
                if (classify(atom) == REQUIRED) {
                    count++;
                }
            }
            return count;
        }

    };

    class learning_skeleton {
    private:
        const std::shared_ptr<arbac_policy> policy;
//        const bool use_admin;
        const overapprox_strategy strategy;
        const role_choicer _role_choicer;

        class b_solver_info {
        };

        class b_solver_state {

        };

        typedef std::shared_ptr<gblock<simple_block_info<b_solver_info>, b_solver_state>> block;

        layer_restriction_info get_required(const std::shared_ptr<arbac_policy> &policy,
                                            const std::vector<std::pair<Expr, Expr>> &target_exprs) {
            layer_restriction_info res;
            for (auto &&expr : target_exprs) {
//                if (use_admin) {
//                    res.in_adm_target.insert(expr.second->atoms().begin(), expr.second->atoms().end());
//                }
                for (auto &&atom : expr.first->atoms()) {
                    if (_role_choicer.classify(atom) != role_choicer::EXCLUDED) {
                        res.in_reg_target.insert(atom);
                    }
                }
            }

            for (auto &&rule : policy->rules()) {
                if (contains(res.in_reg_target, rule->target)) {
                    res.assigning_reg.insert(rule);
//                    if (use_admin) {
//                        res.in_precs.insert(rule->admin->atoms().begin(), rule->admin->atoms().end());
//                    }
                    res.in_reg_precs.insert(rule->prec->atoms().begin(), rule->prec->atoms().end());
                }
            }

            return res;
        };

        int get_layer_block_count(const std::shared_ptr<arbac_policy>& policy,
                                  const layer_restriction_info& infos,
                                  overapprox_strategy strategy) {
            if (strategy.block_count > 0) {
                return strategy.block_count;
            } else {
                int requireds = _role_choicer.get_required_count();
                int dynamic = (int) infos.in_reg_target.size();

                return requireds + dynamic;
            }
        };



    public:

        learning_skeleton(const std::shared_ptr<arbac_policy> _policy,
                          const bool _use_admin,
                          const overapprox_strategy _strategy):
                policy(_policy),
//                use_admin(_use_admin),
                strategy(_strategy),
                role_choicer(simple_role_choicer(policy)) { };

    }

}