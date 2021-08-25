//! Variable elimination by Constant Propagation

/// [A Graph-Free Approach to Data-Flow Analysis][paper].
///
/// [paper]: https://link.springer.com/chapter/10.1007/3-540-45937-5_6
/// (A Graph-Free Approach to Data-Flow Analysis)
/// # TODO
/// - define proper data structures
/// - find dependencies between other reduction strategies
use crate::{
    common::*,
    preproc::{PreInstance, RedStrat},
};

pub struct ConstProp {
    // Removed argument position and propagated term for removed predicates
    const_terms: PrdMap<(usize, Term)>,
}

pub struct FlowGraph;

impl FlowGraph {
    pub fn new(_instance: &Instance) -> Self {
        FlowGraph
    }
}

impl RedStrat for ConstProp {
    fn name(&self) -> &'static str {
        "const_prop"
    }
    fn new(instance: &Instance) -> Self {
        ConstProp {
            const_terms: PrdMap::new(),
        }
    }

    fn apply(&mut self, _instance: &mut PreInstance) -> Res<RedInfo> {
        // 述語ごとに消せる引数を見る
        // 雑に書く
        // # 節を分ける(classify_clause)
        // - 右辺にのみ現れる(right)
        // - 両辺にのみ現れる(implication)
        // - 左辺にのみ現れる(left)
        // # 引数が伝播できるかを見る(check_constpropable??)
        // implicationだけみる
        // にわけて, 両辺に現れる節すべてで, 両辺の呼び出しで引数が同じTerm
        // なら消せる
        // # 消せる時(prop_arg)
        // rightの同じ位置のTerm ri_jを全部集めて, ただ消す
        // implicationも全部消す
        // leftの同じ位置の引数Term liに対して, その節のlhs_termsに
        // ci := ri_0 = li \/ ri_1 = li \/ ... \/ ri_m = liを追加する

        // pull back
        // 最後に求まった解に対して, 伝搬した述語に対応する定数伝搬項ciを追加する?
        // これ正当?
        // ので, ClsIdxとconst_termが要る
        // ClsMap::<RTerm>
        // ??? pull backはどこでする ???
        // どうやってこれをmodelのところにもっていくか
        let total_info = RedInfo::new();
        Ok(total_info)
    }
}
