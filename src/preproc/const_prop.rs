//! Constant Propagation based Argument Reduction

/// Argument Reduction by propagating consistent constants on the pure-rhs clauses.
///
/// An argument of some predicate is propagatable if
/// 1. It is a consistent constant on all of pure-rhs clauses(a predicate application appears on only rhs of clause).
/// 2. Expressions appears on the same argument positions are invariant on implication clauses(a predicate application appears on both sides of clause).
/// # Examples
///
/// ```rust
/// // See this file for a non-trivial example.
/// ::std::fs::OpenOptions::new().read(true).open("rsc/unsat/const_prop.smt2").unwrap();
/// ```
/// # TODO
/// - check the soundness
/// - check the dependencies between other preprocess methods
use crate::{
    common::*,
    preproc::{PreInstance, RedStrat},
};

pub struct ConstProp {
    /// Predicate arguments to keep.
    keep: PrdMap<VarSet>,
    /// Propagated constant terms for each predicates
    const_terms: PrdMap<VarMap<TermSet>>,
}

impl RedStrat for ConstProp {
    fn name(&self) -> &'static str {
        "const_prop"
    }
    fn new(_instance: &Instance) -> Self {
        ConstProp {
            const_terms: PrdMap::new(),
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
        // argumnets' constant conditions to add pure lhs clauses
        let mut const_conditions = ClsHMap::<TermSet>::new();
        'all_preds: for (pred_idx, _pred) in instance.preds().index_iter() {
            // 1. check whether arguments are constant propagatable or not, per predicates
            let (left_clauses, right_clauses) = instance.clauses_of(pred_idx);
            // check the existence of constant expression in arguments on implication clauses
            // TODO: proper error handling
            let both_clauses: HashSet<&ClsIdx> =
                left_clauses.intersection(&right_clauses).collect();
            for &cls_idx in both_clauses {
                let leftargss = &instance[cls_idx].lhs_preds()[&pred_idx];
                let (_p, rightargs) = instance[cls_idx]
                    .rhs()
                    .expect(&format!("{}-clause rhs is broken", cls_idx));

                // check arguments
                for (rightvaridx, rightarg) in rightargs.index_iter() {
                    for leftargs in leftargss {
                        if leftargs[rightvaridx] != *rightarg {
                            self.keep[pred_idx].insert(rightvaridx);
                        }
                    }
                }
            }

            // check if this predicate is already known to be not propable
            if self.keep[pred_idx].len() == instance[pred_idx].sig.len() {
                continue 'all_preds;
            }
            // check rhs-clauses is a single constant ()
            let only_rhs_clauses: HashSet<&ClsIdx> =
                right_clauses.difference(&left_clauses).collect();
            if only_rhs_clauses.len() == 0 {
                for (vid, _ty) in instance[pred_idx].sig.index_iter() {
                    self.keep[pred_idx].insert(vid);
                }
                continue 'all_preds;
            }
            for &cls_idx in only_rhs_clauses {
                let (_p, rightargs) = instance[cls_idx]
                    .rhs()
                    .expect(&format!("{}-clause rhs is broken", cls_idx));
                for (rightvaridx, rightarg) in rightargs.index_iter() {
                    // assemble constnat terms
                    // TODO: confirm RTerm::val(self).is_some() is equivalent to be constant
                    match rightarg.val() {
                        Some(_cstval) => {
                            self.const_terms[pred_idx][rightvaridx].insert(rightarg.clone());
                        }
                        None => {
                            self.keep[pred_idx].insert(rightvaridx);
                        }
                    }
                    // temporary ignore the case constants are more than two kinds.
                    if 2 <= self.const_terms[pred_idx][rightvaridx].len() {
                        self.keep[pred_idx].insert(rightvaridx);
                    }
                }
            }

            // check if this predicate is already known to be not propable
            if self.keep[pred_idx].len() == instance[pred_idx].sig.len() {
                continue 'all_preds;
            }

            // collect propagatable arguments
            for (var_idx, _typ) in instance[pred_idx].sig.index_iter() {
                // this aregument is not propable
                if self.keep[pred_idx].contains(&var_idx) {
                    continue;
                }

                // create constant conditions to add
                for &cls_idx in instance
                    .lhs_clauses_of(pred_idx)
                    .difference(&instance.rhs_clauses_of(pred_idx))
                {
                    let leftargss = &instance[cls_idx].lhs_preds()[&pred_idx];
                    let mut cst_conds = TermSet::new();

                    for leftargs in leftargss {
                        // let mut disj = vec![];
                        // for cst in &self.const_terms[pred_idx][var_idx] {
                        //     disj.push(term::eq(leftargs[var_idx].clone(), cst.clone()))
                        // }
                        // cst_conds.insert(term::or(disj));
                        debug_assert!(self.const_terms[pred_idx][var_idx].len() == 1);
                        for cst in &self.const_terms[pred_idx][var_idx] {
                            cst_conds.insert(term::eq(leftargs[var_idx].clone(), cst.clone()));
                        }
                    }
                    // println!(
                    //     "{}",
                    //     instance[cls_idx].to_string_info(&instance.preds()).unwrap()
                    // );
                    // println!(
                    //     "{}-clause {}-pred {}-arg const cnd: {:#?}",
                    //     cls_idx, pred_idx, var_idx, cst_conds
                    // );
                    const_conditions.insert(cls_idx, cst_conds);
                }
            }
        }

        // return Ok(RedInfo::new());

        // add constant conditions to clauses
        for (cls_idx, cst_conds) in const_conditions {
            for cond in cst_conds {
                instance[cls_idx].insert_term(cond);
            }
        }

        // // 3. remove arguments
        // // just copied from arg_red
        // // TODO: make this proc outside of this function
        let mut res = PrdHMap::new();
        for (pred, vars) in ::std::mem::replace(&mut self.keep, PrdMap::new()).into_index_iter() {
            if !instance[pred].is_defined() {
                let prev = res.insert(pred, vars);
                debug_assert! { prev.is_none() }
            }
        }

        // instance.rm_args(res)
        let redinfo = instance.rm_args(res);
        // check result clauses
        // for (cls_idx, _cst_conds) in instance.clauses().index_iter() {
        //     println!(
        //         "{}",
        //         instance[cls_idx].to_string_info(&instance.preds()).unwrap()
        //     );
        // }
        redinfo
        // Ok(RedInfo::new())
    }
}
impl ConstProp {
    #[allow(dead_code)]
    fn print(&self, instance: &Instance) {
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
        self.keep.clear();

        // Empty constant set for each predicate.
        for (_pred_idx, p) in instance.preds().index_iter() {
            self.keep.push(VarSet::new());
            let mut v = VarMap::new();
            for _ in 0..p.sig.len() {
                v.push(TermSet::new());
            }
            self.const_terms.push(v);
        }
    }
}
