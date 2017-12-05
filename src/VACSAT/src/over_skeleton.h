//
// Created by esteffin on 12/4/17.
//

#ifndef VACSAT_OVER_SKELETON_H
#define VACSAT_OVER_SKELETON_H

#include <vector>
#include <memory>
#include "Policy.h"

namespace SMT {

/*
template <typename LayerInfo, typename BlockInfo>
class node<LayerInfo, BlockInfo> {

};*/

    template <typename LayerInfo, typename BlockInfo>
    class block;

    template <typename LayerInfo, typename BlockInfo>
    class layer {//: public node<LayerInfo, BlockInfo> {
    public:
        int depth;
        std::shared_ptr<LayerInfo> infos;
        std::vector<std::shared_ptr<block<LayerInfo, BlockInfo>>> blocks;

        layer(int _depth,
              std::shared_ptr<LayerInfo> _infos,
              std::vector<std::shared_ptr<block<LayerInfo, BlockInfo>>> _blocks):
                depth(_depth),
                infos(_infos),
                blocks(_blocks) { }
    };

    template <typename LayerInfo, typename BlockInfo>
    class block {//: public node<LayerInfo, BlockInfo> {
    public:
        int depth;
        std::shared_ptr<BlockInfo> infos;
        std::shared_ptr<layer<LayerInfo, BlockInfo>> refinement_layer;

        block(int _depth,
              std::shared_ptr<BlockInfo> _infos,
              std::shared_ptr<layer<LayerInfo, BlockInfo>> _refinement_layer):
                depth(_depth),
                infos(_infos),
                refinement_layer(_refinement_layer) { }


        bool is_leaf() {
            return refinement_layer == false;
        }
    };

    template <typename BlockSolverInfo>
    class simple_block_info {
    public:
        std::vector<rulep> rules;
        Expr invariant;
        std::shared_ptr<BlockSolverInfo> solverInfo;

        simple_block_info(std::vector<rulep> _rules,
                          Expr _invariant,
                          std::shared_ptr<BlockSolverInfo> _solverInfo):
                rules(_rules),
                invariant(_invariant),
                solverInfo(_solverInfo) { }
    };

    template <typename LayerSolverInfo>
    class simple_layer_info {
    public:
        int block_count;
        bool require_nondet_block;
        std::vector<rulep> rules;
        Expr invariant;
        std::shared_ptr<LayerSolverInfo> solverInfo;

        simple_layer_info(int _block_count,
                          bool _require_nondet_block,
                          std::vector<rulep> _rules,
                          Expr _invariant,
                          std::shared_ptr<LayerSolverInfo> _solverInfo):
                block_count(_block_count),
                require_nondet_block(_require_nondet_block),
                rules(_rules),
                invariant(_invariant),
                solverInfo(_solverInfo) { }
    };



}

#endif //VACSAT_OVER_SKELETON_H
