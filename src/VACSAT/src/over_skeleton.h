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

    struct overapprox_strategy {
        int max_depth;
        int block_count;
    };

    template <typename BlockInfo, typename SolverState>
    class gblock {//: public node<LayerInfo, BlockInfo> {
    public:
        tree_path path;
        int uid;
        int depth;
        std::shared_ptr<BlockInfo> infos;
        std::shared_ptr<SolverState> solver_state;
        std::vector<std::shared_ptr<gblock<BlockInfo, SolverState>>> refinement_blocks;

        gblock(tree_path _path,
               int _uid,
               int _depth,
               std::shared_ptr<BlockInfo> _infos,
               std::shared_ptr<SolverState> _solver_state,
               std::vector<std::shared_ptr<gblock<BlockInfo, SolverState>>> _refinement_blocks):
                path(_path),
                uid(_uid),
                depth(_depth),
                infos(_infos),
                solver_state(_solver_state),
                refinement_blocks(_refinement_blocks) { }


        bool is_leaf() {
            return refinement_blocks.empty();
        }
    };

    template <typename BlockSolverInfo>
    class simple_block_info {
    public:
        const std::shared_ptr<arbac_policy>& policy;
        std::vector<rulep> rules;
        std::shared_ptr<BlockSolverInfo> solverInfo;

        simple_block_info(std::shared_ptr<arbac_policy>& _policy,
                          std::vector<rulep> _rules,
                          std::shared_ptr<BlockSolverInfo> _solverInfo):
                policy(_policy),
                rules(_rules),
                solverInfo(_solverInfo) { }
    };
}

#endif //VACSAT_OVER_SKELETON_H
