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

#[derive(Hash, Debug, Clone, Copy)]
enum Position {
    Both,
    Left,
    Right,
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

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        // 消去候補の引数
        'all_preds: for (pred_idx, pred) in instance.preds().index_iter() {
            let mut clause_classified_by_pred: ClsMap<Option<Position>> = ClsMap::new();
            println!("predicate {}, {:#?}", pred_idx, pred);

            // pred's argument is erasable or not
            let mut pred_args_propable: VarMap<bool> = {
                let mut vm = VarMap::with_capacity(instance[pred_idx].sig.len());
                for _ in 0..instance[pred_idx].sig.len() {
                    vm.push(true);
                }
                vm
            };

            //

            for (cls_idx, clause) in instance.clauses().index_iter() {
                println!("{:#?}", instance.preds_of_clause(cls_idx));
                let (pred_apps, head_pred_idx_op) = instance.preds_of_clause(cls_idx);

                let right = match head_pred_idx_op {
                    Some(h_idx) if h_idx == pred_idx => true,
                    _ => false,
                };
                let left = pred_apps.contains_key(&pred_idx);
                let position = if left && right {
                    // check propable
                    let leftargss = &clause.lhs_preds()[&pred_idx];
                    let rightargs = clause
                        .rhs()
                        .expect(&format!("{}-clause rhs is broken", cls_idx))
                        .1;
                    // check arguments
                    for (rightvaridx, rightarg) in rightargs.index_iter() {
                        for leftargs in leftargss {
                            pred_args_propable[rightvaridx] &= leftargs[rightvaridx] == *rightarg;
                        }
                    }
                    if !pred_args_propable.iter().fold(false, |acc, &e| acc || e) {
                        continue 'all_preds;
                    }
                    Some(Position::Both)
                } else if left {
                    Some(Position::Left)
                } else if right {
                    Some(Position::Right)
                } else {
                    None
                };
                // TODO: see why I can't use insert on predmap
                clause_classified_by_pred.push(position);
            }
            // 消せるのを見る
            for (var_idx, _b) in pred_args_propable.index_iter().filter(|(_vid, &b)| b) {
                println!("{:#?}", var_idx);
            }
        }

        // 述語ごとに消せる引数を見る
        // 雑に書く
        // # 節を分ける(classify_clause)
        // - 両辺に現れる(implication)
        // - 右辺にのみ現れる(right)
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
