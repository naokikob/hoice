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
    /// Predicate arguments to keep.
    keep: PrdMap<VarSet>,
    /// Propagated constant terms for removed predicates
    const_terms: PrdMap<VarMap<TermSet>>,
    /// removed arguments of clauses on which propagated predicates appear
    lhs_propable_arguments: ClsMap<PrdMap<VarMap<TermSet>>>,
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
    //    if it's propable, collect const_terms and left clauses' arguments
    // 2. create and add constant constraints to lhs_terms of
    //    propagatable arguments of predicates
    // 3. remove arguments
    // TODO: add constant constraints to model
    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        self.init(&instance);
        let mut const_conditions = ClsHMap::<TermSet>::new();
        'all_preds: for (pred_idx, _pred) in instance.preds().index_iter() {
            // 1. check whether arguments are constant propagatable or not, per predicates
            let (left_clauses, right_clauses) = instance.clauses_of(pred_idx);
            for &cls_idx in left_clauses.intersection(&right_clauses) {
                // check propable
                // TODO: proper error handling
                let leftargss = &instance[cls_idx].lhs_preds()[&pred_idx];
                let (_p, rightargs) = instance[cls_idx]
                    .rhs()
                    .expect(&format!("{}-clause rhs is broken", cls_idx));

                // check arguments
                for (rightvaridx, rightarg) in rightargs.index_iter() {
                    for leftargs in leftargss {
                        if !(leftargs[rightvaridx] == *rightarg) {
                            self.keep[pred_idx].insert(rightvaridx);
                        }
                    }
                }
            }
            // check if this predicate is already known to be not propable
            if self.keep.len() == instance[pred_idx].sig.len() {
                continue 'all_preds;
            }

            for &cls_idx in right_clauses.difference(&left_clauses) {
                let (_p, rightargs) = instance[cls_idx]
                    .rhs()
                    .expect(&format!("{}-clause rhs is broken", cls_idx));
                for (rightvaridx, rightarg) in rightargs.index_iter() {
                    // assemble constnat terms
                    // TODO: confirm val().is_some() is equivalent to be constant
                    match rightarg.val() {
                        Some(cst) => {
                            let cst_term = cst
                                .to_term()
                                .expect("failed to convert val to const terms ");
                            // TODO: init properly because rightvaridx access is failed

                            // self.const_terms[pred_idx].insert(*rightvaridx, TermSet::new());
                            self.const_terms[pred_idx][rightvaridx].insert(cst_term);
                        }
                        None => {
                            self.keep[pred_idx].insert(rightvaridx);
                        }
                    }
                }
            }
            // check if this predicate is already known to be not propable
            if self.keep.len() == instance[pred_idx].sig.len() {
                continue 'all_preds;
            }

            // collect propagatable arguments

            for (var_idx, _typ) in instance[pred_idx].sig.index_iter() {
                // this var is not propable
                if self.keep[pred_idx].contains(&var_idx) {
                    continue;
                }
                // create constant conditions to add
                for &cls_idx in instance.lhs_clauses_of(pred_idx) {
                    let leftargss = &instance[cls_idx].lhs_preds()[&pred_idx];
                    let mut cst_conds = TermSet::new();

                    for leftargs in leftargss {
                        let mut disj = vec![];
                        for cst in &self.const_terms[pred_idx][var_idx] {
                            disj.push(term::eq(leftargs[var_idx].clone(), cst.clone()))
                        }
                        cst_conds.insert(term::or(disj));
                        // self.lhs_propable_arguments[cls_idx][pred_idx][var_idx]
                        //     .insert(leftargs[var_idx].clone());
                    }
                    const_conditions.insert(cls_idx, cst_conds);
                }
            }
        }

        // DEBUG print propable argument (index)
        for (pred_idx, _pred) in instance.preds().index_iter() {
            for (var_idx, _typ) in instance[pred_idx]
                .sig
                .index_iter()
                .filter(|(var_idx, _typ)| !self.keep[pred_idx].contains(var_idx))
            {
                println!("{:#?}", var_idx);
            }
        }

        // create disjunction of constant conditions and add to clauses
        // for (cls_idx, propable_pred_arguments) in self.lhs_propable_arguments.index_iter() {
        //     for (pred_idx, propable_arguments) in propable_pred_arguments.index_iter() {
        //         for (var_idx, argterms) in propable_arguments.index_iter() {
        //             if self.keep[pred_idx].contains(&var_idx) {
        //                 continue;
        //             }
        //             for argterm in argterms {
        //                 let mut disj = vec![];
        //                 for cst in &self.const_terms[pred_idx][var_idx] {
        //                     disj.push(term::eq(argterm.clone(), cst.clone()))
        //                 }
        //                 instance[cls_idx].insert_term(term::or(disj));
        //             }
        //         }
        //     }
        // }

        // // 3. remove arguments
        // // just copied from arg_red
        // // TODO: make this proc outside of this function
        // let mut res = PrdHMap::new();
        // for (pred, vars) in ::std::mem::replace(&mut self.keep, PrdMap::new()).into_index_iter() {
        //     if !instance[pred].is_defined() {
        //         let prev = res.insert(pred, vars);
        //         debug_assert! { prev.is_none() }
        //     }
        // }
        // TODO: add terms to lhs of above
        Ok(RedInfo::new())
        // instance.rm_args(res)
    }
}
impl ConstProp {
    #[allow(dead_code)]
    fn print(&mut self, instance: &Instance) {
        println!("keep {{");
        for (pred, vars) in self.keep.index_iter() {
            if instance[pred].is_defined() {
                continue;
            }
            print!("  {}:", instance[pred]);
            for var in vars {
                print!(" {},", var.default_str())
            }
            println!()
        }
        // println!("}} clauses {{") ;
        // for (idx, _) in instance.clauses().index_iter() {

        // }
        println!("}}")
    }

    fn init(&mut self, instance: &Instance) {
        self.const_terms.clear();
        self.lhs_propable_arguments.clear();
        self.keep.clear();

        // Empty set for each predicate.
        for (_pred_idx, p) in instance.preds().index_iter() {
            self.keep.push(VarSet::new());
            let mut v = VarMap::new();
            for _ in 0..p.sig.len() {
                v.push(TermSet::new());
            }
            self.const_terms.push(v);
        }
        // TODO:
        // for _ in instance.clauses() {
        //     self.lhs_propable_arguments.push(PrdMap::new());
        // }
    }
}
