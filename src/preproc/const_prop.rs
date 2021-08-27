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
    // Removed argument position and propagated constant term for removed predicates
    const_terms: PrdMap<(usize, Term)>,
    keep: PrdMap<VarSet>,
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
    fn new(_instance: &Instance) -> Self {
        ConstProp {
            const_terms: PrdMap::new(),
            keep: PrdMap::new()
        }
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        // TODO: separate initialization
        self.keep.clear();
        // 消去候補の引数
        'all_preds: for (pred_idx, pred) in instance.preds().index_iter() {
            self.keep.push(VarSet::new());
            let mut clause_classified_by_pred: ClsMap<Option<Position>> = ClsMap::new();
            println!("predicate {}, {:#?}", pred_idx, pred);

            
            // pred's argument is erasable or not
            

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
                    // TODO: proper error handling
                    let leftargss = &clause.lhs_preds()[&pred_idx];
                    let rightargs = 
                    if let Some((_prdidx, rightargs)) = clause
                        .rhs() {
                            rightargs 
                        }else {
                            panic!("{}-clause rhs is broken", cls_idx);
                        };
                        
                        
                    // check arguments
                    for (rightvaridx, rightarg) in rightargs.index_iter() {
                        for leftargs in leftargss {
                            if !(leftargs[rightvaridx] == *rightarg) {
                                self.keep[pred_idx].insert(rightvaridx);
                            }
                        }
                    }
                    // check already this predicate is not propable
                    if self.keep.len() == instance[pred_idx].sig.len() {
                        continue 'all_preds;
                    }
                    Some(Position::Both)
                } else if left {
                    Some(Position::Left)
                } else if right {
                    // check if the argument is constant.
                    let rightargs = 
                    if let Some((_prdidx, rightargs)) = clause
                        .rhs() {
                            rightargs 
                        }else {
                            panic!("{}-clause rhs is broken", cls_idx);
                        };
                        for (rightvaridx, rightarg) in rightargs.index_iter() {
                            // pred_args_propable[rightvaridx] &= rightarg.val().is_some();
                            // TODO: check val().is_some() is equivalent to be constant 
                            if !rightarg.val().is_some() {
                                self.keep[pred_idx].insert(rightvaridx);
                            }
                        }
                        // check already this predicate is not propable
                        if self.keep.len() == instance[pred_idx].sig.len() {
                            continue 'all_preds;
                        }

                    Some(Position::Right)
                } else {
                    None
                };
                // TODO: see why I can't use insert on predmap
                clause_classified_by_pred.push(position);
            }
            // 消せるのを見る
            for (var_idx, _typ) in instance[pred_idx].sig.index_iter().filter(|(var_idx, _typ) |self.keep[pred_idx].contains(var_idx)) {
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
        // implicationの両辺に現れる節すべてで, 両辺の呼び出しで引数が同じTerm
        // かつ, すべてのrightで定数
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
