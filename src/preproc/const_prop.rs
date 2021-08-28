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
    const_terms: PrdMap<VarMap<TermSet>>,

    lhs_propable_arguments: ClsMap<PrdMap<VarMap<TermSet>>>,
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
            lhs_propable_arguments: ClsMap::new(),
            keep: PrdMap::new(),
        }
    }

    // 1. check arguments are constant propagatable or not, per predicates
    // 2. create and add constant constraints to lhs_terms of
    //    propagatable arguments of predicates
    // 3. remove arguments
    // TODO: add constant constraints to model
    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        // TODO: separate initialization
        self.keep.clear();
        'all_preds: for (pred_idx, pred) in instance.preds().index_iter() {
            self.keep.push(VarSet::new());
            self.const_terms.push(VarMap::new());
            let mut clause_classified_by_pred: ClsMap<Option<Position>> = ClsMap::new();
            println!("predicate {}, {:#?}", pred_idx, pred);

            // 1. check arguments are constant propagatable or not, per predicates

            for (cls_idx, clause) in instance.clauses().index_iter() {
                // println!("{:#?}", instance.preds_of_clause(cls_idx));
                // TODO: remove loop by using Instance::clauses_of(p: Pred)
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
                    let rightargs = if let Some((_prdidx, rightargs)) = clause.rhs() {
                        rightargs
                    } else {
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
                    Some(Position::Both)
                } else if left {
                    Some(Position::Left)
                } else if right {
                    // check if the argument is constant.
                    let rightargs = if let Some((_prdidx, rightargs)) = clause.rhs() {
                        rightargs
                    } else {
                        panic!("{}-clause rhs is broken", cls_idx);
                    };
                    for (rightvaridx, rightarg) in rightargs.index_iter() {
                        // assemble constnat terms
                        // TODO: confirm val().is_some() is equivalent to be constant
                        match rightarg.val() {
                            Some(cst) => {
                                let cst_term =
                                    cst.to_term().expect("failed to create const terms ");
                                self.const_terms[pred_idx][rightvaridx].insert(cst_term);
                            }
                            None => drop(self.keep[pred_idx].insert(rightvaridx)),
                        }
                    }
                    Some(Position::Right)
                } else {
                    None
                };

                // check already this predicate is not propable
                if self.keep.len() == instance[pred_idx].sig.len() {
                    continue 'all_preds;
                }
                // TODO: see why I can't use insert on predmap
                clause_classified_by_pred.push(position);
            }

            // 2. create and add constant constraints
            // collect lhs's propable argument per one clause and
            // add term which corresponds to constant conditions

            for (var_idx, _typ) in instance[pred_idx].sig.index_iter() {
                if self.keep[pred_idx].contains(&var_idx) {
                    continue;
                }
                // collect argument from every appearance of pred in lhs
                for &cls_idx in instance.lhs_clauses_of(pred_idx) {
                    let leftargss = &instance[cls_idx].lhs_preds()[&pred_idx];
                    for leftargs in leftargss {
                        self.lhs_propable_arguments[cls_idx][pred_idx][var_idx]
                            .insert(leftargs[var_idx].clone());
                    }
                }
            }
        }

        // DEBUG print propable argument (index)
        for (pred_idx, pred) in instance.preds().index_iter() {
            for (var_idx, _typ) in instance[pred_idx]
                .sig
                .index_iter()
                .filter(|(var_idx, _typ)| !self.keep[pred_idx].contains(var_idx))
            {
                println!("{:#?}", var_idx);
            }
        }

        // 3. remove arguments
        // just copied from arg_red
        // TODO: make this proc outside of this function
        let mut res = PrdHMap::new();
        for (pred, vars) in ::std::mem::replace(&mut self.keep, PrdMap::new()).into_index_iter() {
            if !instance[pred].is_defined() {
                let prev = res.insert(pred, vars);
                debug_assert! { prev.is_none() }
            }
        }
        // TODO: add terms to lhs of above
        instance.rm_args(res)
    }
}
