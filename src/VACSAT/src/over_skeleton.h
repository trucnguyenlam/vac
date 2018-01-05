//
// Created by esteffin on 12/4/17.
//

#ifndef VACSAT_OVER_SKELETON_H
#define VACSAT_OVER_SKELETON_H

#include <vector>
#include <memory>
#include "Policy.h"

namespace SMT {

    class role_choicer {
    public:
        enum Choice {
            REQUIRED,
            FREE,
            EXCLUDED
        };
        virtual Choice classify(atomp r) const = 0;
        virtual int get_required_count() const = 0;
    };

    typedef std::list<int> tree_path;
    std::string tree_path_to_string(tree_path& path) {
        std::string ret = "_root";
        for (auto &&p : path) {
            ret = ret + "_" + std::to_string(p);
        }
        return ret + "_";
    }

    struct overapprox_restriction {
        std::vector<bool> interesting_var;
        std::vector<bool> interesting_rule;

        int interesting_var_count;
        int interesting_rule_count;
    };

    struct overapprox_strategy {
        int max_depth;
        int block_count;
    };

    template <typename BlockInfo, typename SolverState>
    class gblock {//: public node<LayerInfo, BlockInfo> {
    public:
        tree_path path;
        std::string uid;
        int depth;
        std::shared_ptr<BlockInfo> infos;
        std::shared_ptr<SolverState> solver_state;
        std::list<std::weak_ptr<gblock<BlockInfo, SolverState>>> ancestors;
        std::vector<std::shared_ptr<gblock<BlockInfo, SolverState>>> refinement_blocks;

        gblock(std::string _uid,
               int _depth):
                path(std::list<int>()),
                uid(_uid),
                depth(_depth),
                infos(nullptr),
                solver_state(nullptr),
                ancestors(std::list<std::weak_ptr<gblock<BlockInfo, SolverState>>>()),
                refinement_blocks(std::vector<std::shared_ptr<gblock<BlockInfo, SolverState>>>()) { }

        gblock(tree_path _path,
               int _depth,
               std::shared_ptr<BlockInfo> _infos,
               std::list<std::weak_ptr<gblock<BlockInfo, SolverState>>> _ancestors):
                path(_path),
                uid(tree_path_to_string(_path)),
                depth(_depth),
                infos(_infos),
                solver_state(nullptr),
                ancestors(_ancestors),
                refinement_blocks(std::vector<std::shared_ptr<gblock<BlockInfo, SolverState>>>()) { }

        gblock(tree_path _path,
               std::string _uid,
               int _depth,
               std::shared_ptr<BlockInfo> _infos,
               std::shared_ptr<SolverState> _solver_state,
               std::list<std::weak_ptr<gblock<BlockInfo, SolverState>>> _ancestors,
               std::vector<std::shared_ptr<gblock<BlockInfo, SolverState>>> _refinement_blocks):
                path(_path),
                uid(_uid),
                depth(_depth),
                infos(_infos),
                solver_state(_solver_state),
                ancestors(_ancestors),
                refinement_blocks(_refinement_blocks) { }


        bool is_leaf() {
            return refinement_blocks.empty();
        }
        bool is_root() {
            return depth == 0;
        }
    };

    template <typename BlockSolverInfo>
    class simple_block_info {
    public:
        const std::shared_ptr<arbac_policy>& policy;
        std::vector<rulep> rules;
        std::shared_ptr<BlockSolverInfo> solverInfo;
        const Expr invariant;

        simple_block_info(const std::shared_ptr<arbac_policy>& _policy,
                          std::vector<rulep> _rules,
                          std::shared_ptr<BlockSolverInfo> _solverInfo,
                          Expr _invariant):
                policy(_policy),
                rules(_rules),
                solverInfo(_solverInfo),
                invariant(_invariant) { }
    };

}

#endif //VACSAT_OVER_SKELETON_H
