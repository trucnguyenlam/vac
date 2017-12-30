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

    template <typename LayerInfo, typename BlockInfo>
    class gblock;

    template <typename LayerInfo, typename BlockInfo>
    class glayer {//: public node<LayerInfo, BlockInfo> {
    public:
        tree_path path;
        int uid;
        int depth;
        std::shared_ptr<LayerInfo> infos;
        std::vector<std::shared_ptr<gblock<LayerInfo, BlockInfo>>> blocks;

        glayer(tree_path _path,
               int _uid,
               int _depth,
               std::shared_ptr<LayerInfo> _infos,
               std::vector<std::shared_ptr<gblock<LayerInfo, BlockInfo>>> _blocks):
                path(_path),
                uid(_uid),
                depth(_depth),
                infos(_infos),
                blocks(_blocks) { }
    };

    template <typename LayerInfo, typename BlockInfo>
    class gblock {//: public node<LayerInfo, BlockInfo> {
    public:
        tree_path path;
        int uid;
        int depth;
        std::shared_ptr<BlockInfo> infos;
        std::shared_ptr<glayer<LayerInfo, BlockInfo>> refinement_layer;

        gblock(tree_path _path,
               int _uid,
               int _depth,
               std::shared_ptr<BlockInfo> _infos,
               std::shared_ptr<glayer<LayerInfo, BlockInfo>> _refinement_layer):
                path(_path),
                uid(_uid),
                depth(_depth),
                infos(_infos),
                refinement_layer(_refinement_layer) { }


        bool is_leaf() {
            return refinement_layer == false;
        }
    };

    template <typename LayerSolverInfo>
    class simple_layer_info {
    public:
        const std::shared_ptr<arbac_policy>& policy;
        int block_count;
        bool require_nondet_block;
        std::vector<rulep> rules;
        Expr target_rule;
        Expr invariant;
        std::shared_ptr<LayerSolverInfo> solverInfo;

        simple_layer_info(std::shared_ptr<arbac_policy>& _policy,
                          int _block_count,
                          bool _require_nondet_block,
                          std::vector<rulep> _rules,
                          Expr _target_rule,
                          Expr _invariant,
                          std::shared_ptr<LayerSolverInfo> _solverInfo):
                policy(_policy),
                block_count(_block_count),
                require_nondet_block(_require_nondet_block),
                rules(_rules),
                target_rule(_target_rule),
                invariant(_invariant),
                solverInfo(_solverInfo) { }
    };

    template <typename BlockSolverInfo>
    class simple_block_info {
    public:
        const std::shared_ptr<arbac_policy>& policy;
        std::vector<rulep> rules;
        Expr invariant;
        std::shared_ptr<BlockSolverInfo> solverInfo;

        simple_block_info(std::shared_ptr<arbac_policy>& _policy,
                          std::vector<rulep> _rules,
                          Expr _invariant,
                          std::shared_ptr<BlockSolverInfo> _solverInfo):
                policy(_policy),
                rules(_rules),
                invariant(_invariant),
                solverInfo(_solverInfo) { }
    };
}

#endif //VACSAT_OVER_SKELETON_H
