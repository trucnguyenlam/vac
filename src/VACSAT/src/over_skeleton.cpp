//
// Created by esteffin on 12/5/17.
//

#include "over_skeleton.h"

namespace SMT {

    template <typename LayerInfo, typename BlockInfo>
    layer<LayerInfo, BlockInfo>::layer(int _depth,
                 std::shared_ptr<LayerInfo> _infos,
                 std::vector<std::shared_ptr<block<LayerInfo, BlockInfo>>> _blocks):
            depth(_depth),
            infos(_infos),
            blocks(_blocks) { };



    template <typename LayerInfo, typename BlockInfo>
    block<LayerInfo, BlockInfo>::block(int _depth,
                 std::shared_ptr<BlockInfo> _infos,
                 std::shared_ptr<layer<LayerInfo, BlockInfo>> _refinement_layer):
            depth(_depth),
            infos(_infos),
            refinement_layer(_refinement_layer) { };

    bool block<LayerInfo, BlockInfo>::is_leaf() {
        return refinement_layer == nullptr;
    };

    template <typename BlockSolverInfo>
    simple_block_info<BlockSolverInfo>::simple_block_info(std::vector<rulep> _rules,
                                         Expr _invariant,
                                         std::shared_ptr<BlockSolverInfo> _solverInfo):
        rules(_rules),
        invariant(_invariant),
        solverInfo(_solverInfo) { }



    template <typename LayerSolverInfo>
    simple_layer_info<LayerSolverInfo>::simple_layer_info(int _block_count,
                                         bool _require_nondet_block,
                                         std::vector<rulep> _rules,
                                         Expr _invariant,
                                         std::shared_ptr<LayerSolverInfo> _solverInfo):
            block_count(_block_count),
            require_nondet_block(_require_nondet_block),
            rules(_rules),
            invariant(_invariant),
            solverInfo(_solverInfo) { }

}