//! Actual instance structure.

use common::* ;
use instance::info::* ;

/// A clause.
///
/// Fields are public because a clause is important only if it's in the
/// instance, from which it can only be accessed immutably.
///
/// # Invariants
///
/// - if `! vars[var].active`, then `var` does not appear in `lhs` or `rhs`
#[derive(Clone)]
pub struct Clause {
  /// Variables of the clause.
  pub vars: VarMap<VarInfo>,
  /// Terms of the left-hand side.
  lhs_terms: HConSet<RTerm>,
  /// Predicate applications of the left-hand side.
  lhs_preds: PredApps,
  /// Single term right-hand side.
  rhs: TTerm,
}
impl Clause {
  /// Creates a clause.
  pub fn new(
    vars: VarMap<VarInfo>, lhs: Vec<TTerm>, rhs: TTerm
  ) -> Self {
    let lhs_terms = HConSet::with_capacity( lhs.len() ) ;
    let lhs_preds = PredApps::with_capacity( lhs.len() ) ;
    let mut clause = Clause { vars, lhs_terms, lhs_preds, rhs } ;
    for tterm in lhs { clause.lhs_insert(tterm) ; }
    clause
  }

  /// Checks a clause is well-formed.
  #[cfg(debug_assertions)]
  pub fn check(& self, blah: & 'static str) -> Res<()> {
    use std::iter::Extend ;
    let mut vars = VarSet::with_capacity( self.vars.len() ) ;
    for term in & self.lhs_terms {
      vars.extend( term.vars() )
    }
    for (_, argss) in & self.lhs_preds {
      for args in argss {
        for arg in args {
          vars.extend( arg.vars() )
        }
      }
    }
    vars.extend( self.rhs.vars() ) ;
    for var in vars {
      if ! self.vars[var].active {
        bail!(
          "ill-formed clause: {}, \
          variable {} appears in the clause but is not active",
          blah, self[var]
        )
      }
    }
    Ok(())
  }
  #[cfg(not(debug_assertions))]
  #[inline(always)]
  pub fn check(& self, _: & 'static str) -> Res<()> {
    Ok(())
  }

  /// Deactivates a variable.
  pub fn deactivate(& mut self, var: VarIdx) -> Res<()> {
    debug_assert!( self.vars[var].active ) ;
    self.vars[var].active = false ;
    self.check( "after `deactivate`" )
  }

  /// Inserts a top term in the lhs. Returns true if it was not there.
  #[inline(always)]
  pub fn lhs_insert(& mut self, tterm: TTerm) -> bool {
    match tterm {
      TTerm::T(term) => if let Some(true) = term.bool() {
        false
      } else {
        self.insert_term(term)
      },
      TTerm::P { pred, args } => self.insert_pred_app(pred, args),
    }
  }

  /// Inserts a predicate application in the LHS.
  ///
  /// Returns true if the predicate application is new.
  #[inline(always)]
  pub fn insert_pred_app(
    & mut self, pred: PrdIdx, args: VarMap<Term>
  ) -> bool {
    self.lhs_preds.insert_pred_app(pred, args)
  }

  /// Inserts a term in an LHS. Externalized for ownership reasons.
  fn lhs_insert_term(lhs_terms: & mut HConSet<RTerm>, term: Term) -> bool {
    if let Some(kids) = term.conj_inspect() {
      let mut new_stuff = false ;
      let mut stack = vec![] ;
      for kid in kids {
        if let Some(kids) = kid.conj_inspect() {
          for kid in kids { stack.push(kid) }
        } else if let Some(true) = term.bool() {
          ()
        } else {
          let is_new = lhs_terms.insert( kid.clone() ) ;
          new_stuff = new_stuff || is_new
        }
      }
      while let Some(term) = stack.pop() {
        if let Some(kids) = term.conj_inspect() {
          for kid in kids { stack.push(kid) }
        } else if let Some(true) = term.bool() {
          ()
        } else {
          let is_new = lhs_terms.insert( term.clone() ) ;
          new_stuff = new_stuff || is_new
        }
      }
      return new_stuff
    }

    // Only reachable when `term.conj_inspect()` is `None`. Needs to be outside
    // the match because of lexical lifetimes.
    if let Some(true) = term.bool() {
      false
    } else {
      lhs_terms.insert(term)
    }
  }

  /// Inserts a term in the LHS.
  pub fn insert_term(& mut self, term: Term) -> bool {
    Self::lhs_insert_term(& mut self.lhs_terms, term)
  }

  /// Length of a clause's LHS.
  #[inline(always)]
  pub fn lhs_len(& self) -> usize {
    self.lhs_terms.len() + self.lhs_preds.len()
  }
  /// True if the clause's LHS is empty.
  #[inline(always)]
  pub fn lhs_is_empty(& self) -> bool {
    self.lhs_terms.is_empty() && self.lhs_preds.is_empty()
  }

  /// LHS accessor (terms).
  #[inline(always)]
  pub fn lhs_terms(& self) -> & HConSet<RTerm> {
    & self.lhs_terms
  }
  /// LHS accessor (predicate applications).
  #[inline(always)]
  pub fn lhs_preds(& self) -> & PredApps {
    & self.lhs_preds
  }
  /// Number of predicate applications in the lhs (>= number of predicates).
  pub fn lhs_pred_apps_len(& self) -> usize {
    let mut sum = 0 ;
    for argss in self.lhs_preds.values() {
      sum += argss.len()
    }
    sum
  }
  /// RHS accessor.
  #[inline(always)]
  pub fn rhs(& self) -> & TTerm {
    & self.rhs
  }

  /// Variables accessor.
  #[inline(always)]
  pub fn vars(& self) -> & VarMap<VarInfo> {
    & self.vars
  }

  /// Clones a clause but changes the rhs.
  #[inline(always)]
  pub fn clone_with_rhs(& self, rhs: TTerm) -> Self {
    Clause {
      vars: self.vars.clone(),
      lhs_terms: self.lhs_terms.clone(),
      lhs_preds: self.lhs_preds.clone(),
      rhs,
    }
  }



  /// Variable substitution.
  ///
  /// Returns a boolean indicating whether any substitution occured.
  ///
  /// Used for substitutions in the same clause / predicate scope.
  pub fn subst<Map: VarIndexed<Term>>(
    & mut self, map: & Map
  ) -> bool {
    let mut changed = false ;
    let mut lhs_terms = HConSet::with_capacity( self.lhs_terms.len() ) ;
    ::std::mem::swap(& mut lhs_terms, & mut self.lhs_terms) ;
    for term in lhs_terms.drain() {
      let (term, b) = term.subst(map) ;
      self.insert_term(term) ;
      changed = changed || b
    }
    let mut nu_argss = VarMapSet::with_capacity(7) ;
    for (_, argss) in & mut self.lhs_preds {
      debug_assert!( nu_argss.is_empty() ) ;
      for mut args in argss.drain() {
        for arg in args.iter_mut() {
          let (nu_arg, b) = arg.subst(map) ;
          * arg = nu_arg ;
          changed = changed || b
        }
        nu_argss.insert(args) ;
      }
      ::std::mem::swap(& mut nu_argss, argss)
    }
    let rhs_changed = self.rhs.subst(map) ;
    changed = changed || rhs_changed ;
    changed
  }

  /// Adds fresh variables to the clause for each of the input variables.
  /// Returns a map from the input variables to the fresh ones (as terms).
  ///
  /// Used when inlining a predicate with quantified variables.
  fn fresh_vars_for(& mut self, vars: & Qualfed) -> VarHMap<Term> {
    let mut map = VarHMap::with_capacity( vars.len() ) ;
    for (var, typ) in vars {
      let fresh = self.vars.next_index() ;
      let fresh_name = format!("hoice_fresh_var@{}", fresh) ;
      let info = VarInfo::new(fresh_name, * typ, fresh) ;
      self.vars.push(info) ;
      let _prev = map.insert(* var, term::var(fresh)) ;
      debug_assert!( _prev.is_none() )
    }
    map
  }

  // /// Replaces a predicate application by some top terms.
  // ///
  // /// Does not preserve the order of the top terms.
  // pub fn subst_top(& mut self, pred: PrdIdx, top) -> 

  /// Writes a clause given a special function to write predicates.  
  fn write<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & VarMap<Term>) -> IoRes<()> {
    use common::consts::keywords ;

    write!(w, "({} ({}\n  (", keywords::assert, keywords::forall) ? ;
    let mut inactive = 0 ;
    for var in & self.vars {
      if var.active {
        write!(w, " ({} {})", var.name, var.typ) ?
      } else {
        inactive += 1 ;
      }
    }
    write!(w, " )") ? ;
    if inactive > 0 {
      write!(w, " ; {} inactive variable(s)", inactive) ?
    }
    write!(w, "\n") ? ;

    let lhs_len = self.lhs_len() ;

    let (pref, suff) = if lhs_len != 0 {
      write!(w, "  (=>") ? ;
      let (pref, suff) = if lhs_len > 1 {
        write!(w, "\n    (and") ? ;
        ("      ", Some("    )"))
      } else {
        ("    ", None)
      } ;

      for term in & self.lhs_terms {
        write!(w, "\n{}", pref) ? ;
        term.write(w, |w, var| w.write_all( self.vars[var].as_bytes() )) ?
      }
      for (pred, argss) in & self.lhs_preds {
        for args in argss {
          write!(w, "\n{}", pref) ? ;
          write_prd(w, * pred, args) ?
        }
      }

      write!(w, "\n") ? ;
      if let Some(suff) = suff {
        write!(w, "{}\n", suff) ?
      }
      ("    ", Some("  )"))
    } else {
      ("  ", None)
    } ;

    write!(w, "{}", pref) ? ;
    self.rhs.write(
      w, |w, var| w.write_all( self.vars[var].as_bytes() ), & write_prd
    ) ? ;
    write!(w, "\n") ? ;
    if let Some(suff) = suff {
      write!(w, "{}\n", suff) ?
    }
    write!(w, "))")
  }
}
impl ::std::ops::Index<VarIdx> for Clause {
  type Output = VarInfo ;
  fn index(& self, index: VarIdx) -> & VarInfo {
    & self.vars[index]
  }
}
impl<'a> ::rsmt2::to_smt::Expr2Smt<
  (& 'a PrdSet, & 'a PrdSet, & 'a PrdMap<PrdInfo>)
> for Clause {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, info: & (
      & 'a PrdSet, & 'a PrdSet, & 'a PrdMap<PrdInfo>
    )
  ) -> SmtRes<()> {
    let (ref true_preds, ref false_preds, ref prd_info) = * info ;
    write!(writer, "(not ") ? ;
    if ! self.lhs_is_empty() {
      write!(writer, "(=> (and") ?
    }
    for term in & self.lhs_terms {
      writer.write_all( " ".as_bytes() ) ? ;
      term.write( writer, |w, var| var.default_write(w) ) ?
    }
    for (pred, argss) in & self.lhs_preds {
      if true_preds.contains(pred) {
        writer.write_all( " true".as_bytes() ) ?
      } else if false_preds.contains(pred) {
        writer.write_all( " false".as_bytes() ) ?
      } else {
        for args in argss {
          writer.write_all( " (".as_bytes() ) ? ;
          writer.write_all( prd_info[* pred].name.as_bytes() ) ? ;
          for arg in args {
            writer.write_all( " ".as_bytes() ) ? ;
            arg.write(writer, |w, var| var.default_write(w)) ?
          }
          writer.write_all( ")".as_bytes() ) ?
        }
      }
    }
    if ! self.lhs_is_empty() {
      write!(writer, ") ") ?
    }
    self.rhs.write_smt2(
      writer, |w, prd, args| {
        if true_preds.contains(& prd) {
          write!(w, "true")
        } else if false_preds.contains(& prd) {
          write!(w, "false")
        } else {
          write!(w, "({}", prd_info[prd].name) ? ;
          for arg in args {
            write!(w, " ") ? ;
            arg.write(w, |w, var| var.default_write(w)) ?
          }
          write!(w, ")")
        }
      }
    ) ? ;
    if ! self.lhs_is_empty() {
      write!(writer, ")") ?
    }
    write!(writer, ")") ? ;
    Ok(())
  }
}




/// Stores the instance: the clauses, the factory and so on.
///
/// # NB
///
/// Clause indices can vary during instance building, because of the
/// simplifications that can remove clauses.
///
/// So, `pred_to_clauses` has to be carefully maintained, the easiest way to
/// do this is to never access an instance's fields directly from the outside.
pub struct Instance {
  /// Constants constructed so far.
  consts: HConSet<RTerm>,
  /// Predicates.
  preds: PrdMap<PrdInfo>,
  /// Predicates for which a suitable term has been found.
  pred_terms: PrdMap< Option< TTerms > >,
  /// Predicates for which a suitable quantified term has been found.
  pred_qterms: PrdMap< Option< (VarHMap<Typ>, TTerms) > >,
  /// Predicates defined in `pred_terms`, sorted by predicate dependencies.
  ///
  /// Populated by the `finalize` function.
  sorted_pred_terms: Vec<PrdIdx>,
  /// Max arity of the predicates.
  pub max_pred_arity: Arity,
  /// Clauses.
  clauses: ClsMap<Clause>,
  /// Maps predicates to the clauses where they appear in the lhs and rhs
  /// respectively.
  pred_to_clauses: PrdMap< (ClsSet, ClsSet) >,
  /// Clause simplifier.
  simplifier: ClauseSimplifier,
  /// Unsat flag.
  is_unsat: bool,
}
impl Instance {
  /// Instance constructor.
  pub fn new() -> Instance {
    let pred_capa = conf.instance.pred_capa ;
    let clause_capa = conf.instance.clause_capa ;
    let mut instance = Instance {
      consts: HConSet::with_capacity(103),
      preds: PrdMap::with_capacity(pred_capa),
      pred_terms: PrdMap::with_capacity(pred_capa),
      pred_qterms: PrdMap::with_capacity(pred_capa),
      sorted_pred_terms: Vec::with_capacity(pred_capa),
      max_pred_arity: 0.into(),
      clauses: ClsMap::with_capacity(clause_capa),
      pred_to_clauses: PrdMap::with_capacity(pred_capa),
      simplifier: ClauseSimplifier::new(),
      is_unsat: false,
    } ;
    // Create basic constants, adding to consts to have mining take them into account.
    let (wan,too) = (term::one(), term::zero()) ;
    instance.consts.insert(wan) ;
    instance.consts.insert(too) ;
    instance
  }

  /// Sets the unsat flag in the instance.
  pub fn set_unsat(& mut self) {
    self.is_unsat = true
  }

  /// True if a predicate is forced to something.
  #[inline]
  pub fn is_known(& self, pred: PrdIdx) -> bool {
    self.pred_terms[pred].is_some() ||
    self.pred_qterms[pred].is_some()
  }

  /// Returns the model corresponding to the input predicates and the forced
  /// predicates.
  ///
  /// The model is sorted in topological order.
  pub fn model_of(& self, candidates: Candidates) -> Res<Model> {
    use std::iter::Extend ;
    let mut model = Model::with_capacity( self.preds.len() ) ;
    model.extend(
      candidates.into_index_iter().filter_map(
        |(pred, tterms_opt)| tterms_opt.map(
          |term| (pred, None, TTerms::of_tterm( TTerm::T(term) ))
        )
      )
    ) ;
    for pred in & self.sorted_pred_terms {
      let pred = * pred ;
      if let Some(ref tterms) = self.pred_terms[pred] {
        model.push( (pred, None, tterms.clone()) )
      } else if let Some((ref qualfed, ref tterms)) = self.pred_qterms[pred] {
        model.push( (pred, Some(qualfed.clone()), tterms.clone()) )
      } else {
        bail!("inconsistency in sorted forced predicates")
      }
    }
    Ok( model )
  }

  /// Returns a model for the instance when all the predicates have terms
  /// assigned to them.
  pub fn is_trivial(& self) -> Res< Option< Option<Model> > > {
    if self.is_unsat { Ok( Some(None) ) } else {
      for pred in self.pred_indices() {
        if self.pred_terms[pred].is_none()
        && self.pred_qterms[pred].is_none() {
          return Ok(None)
        }
      }
      // Only reachable if all elements of `self.pred_terms` are `Some(_)`.
      self.model_of( vec![].into() ).map(|res| Some(Some(res)))
    }
  }


  /// Clauses a predicate appears in. Lhs and rhs.
  pub fn clauses_of_pred(& self, pred: PrdIdx) -> ( & ClsSet, & ClsSet ) {
    ( & self.pred_to_clauses[pred].0, & self.pred_to_clauses[pred].1 )
  }
  /// Clauses a predicate appears in. Lhs and rhs.
  #[inline]
  pub fn preds_of_clause(
    & self, clause: ClsIdx
  ) -> (& PredApps, Option<PrdIdx>) {
    (self[clause].lhs_preds(), self[clause].rhs().pred())
  }


  /// Prints some top terms as a model.
  ///
  /// Meaning variables are printed with default printing: `<var_idx>` is
  /// printed as `v_<var_idx>`.
  pub fn print_tterms_as_model<W: Write>(
    & self, w: & mut W, tterms: & TTerms
  ) -> ::std::io::Result<()> {
    tterms.write(
      w, |w, var| var.default_write(w),
      |w, pred, args| {
        write!(w, "({}", self[pred]) ? ;
        for arg in args {
          write!(w, " {}", arg) ?
        }
        write!(w, ")")
      }
    )
  }

  /// Finalizes instance creation.
  ///
  /// - shrinks all collections
  /// - sorts forced predicates by dependencies
  ///
  /// # TO DO
  ///
  /// - optimize sorting of forced preds by dependencies (low priority)
  pub fn finalize(& mut self) {
    self.consts.shrink_to_fit() ;
    self.preds.shrink_to_fit() ;
    self.pred_terms.shrink_to_fit() ;
    self.clauses.shrink_to_fit() ;

    let mut tmp: Vec< (PrdIdx, PrdSet) > = Vec::with_capacity(
      self.preds.len()
    ) ;

    // Populate `tmp`.
    let mut known_preds = PrdSet::with_capacity( self.preds.len() ) ;
    for pred in self.pred_indices() {
      if let Some(ref tterms) = self.pred_terms[pred] {
        tmp.push( (pred, tterms.preds()) )
      } else if let Some((_, ref tterms)) = self.pred_qterms[pred] {
        tmp.push( (pred, tterms.preds()) )
      } else {
        known_preds.insert(pred) ;
      }
    }
    // Sort by dependencies.
    while ! tmp.is_empty() {
      let mut cnt = 0 ; // Will use swap remove.
      'find_preds: while cnt < tmp.len() {
        for pred in & tmp[cnt].1 {
          if ! known_preds.contains(pred) {
            // Don't know this predicate, keep going in `tmp`.
            cnt += 1 ;
            continue 'find_preds
          }
        }
        // Reachable only we already have all of the current pred's
        // dependencies.
        let (pred, _) = tmp.swap_remove(cnt) ;
        self.sorted_pred_terms.push(pred) ;
        known_preds.insert(pred) ;
        () // No `cnt` increment after swap remove.
      }
    }

    self.sorted_pred_terms.shrink_to_fit()
  }


  /// Returns the term we already know works for a predicate, if any.
  pub fn forced_terms_of(& self, pred: PrdIdx) -> Option<(
    Option<& Qualfed>, & TTerms
  )> {
    if let Some(tterms) = self.pred_terms[pred].as_ref() {
      Some( (None, tterms) )
    } else {
      self.pred_qterms[pred].as_ref().map(
        |& (ref quals, ref tterms)| (Some(quals), tterms)
      )
    }
  }

  /// If the input predicate is forced to a constant boolean, returns its
  /// value.
  pub fn bool_value_of(& self, pred: PrdIdx) -> Option<bool> {
    self.forced_terms_of(pred).and_then(
      |(_, terms)| terms.bool()
    )
  }

  /// Forced predicates in topological order.
  pub fn sorted_forced_terms(& self) -> & Vec<PrdIdx> {
    & self.sorted_pred_terms
  }

  /// Returns the clauses in which the predicate appears in the lhs and rhs
  /// respectively.
  pub fn clauses_of(& self, pred: PrdIdx) -> (& ClsSet, & ClsSet) {
    (& self.pred_to_clauses[pred].0, & self.pred_to_clauses[pred].1)
  }

  /// Adds some terms to the lhs of a clause.
  ///
  /// Updates `pred_to_clauses`.
  pub fn clause_lhs_extend<I: IntoIterator<Item = TTerm>>(
    & mut self, clause_idx: ClsIdx, tterms: I
  ) {
    let clause = & mut self.clauses[clause_idx] ;
    for tterm in tterms.into_iter() {
      match tterm {
        TTerm::P { pred, args } => {
          self.pred_to_clauses[pred].0.insert(clause_idx) ;
          clause.insert_pred_app(pred, args) ;
        },
        TTerm::T(term) => {
          clause.insert_term(term) ;
        },
      }
    }
  }

  /// Replaces the rhs of a clause.
  ///
  /// Updates `pred_to_clauses` for the term it inserts but **not** the one it
  /// removes.
  pub fn clause_rhs_force(
    & mut self, clause_idx: ClsIdx, tterm: TTerm
  ) {
    let clause = & mut self.clauses[clause_idx] ;
    if let Some(pred) = tterm.pred() {
      let is_new = self.pred_to_clauses[pred].1.insert(clause_idx) ;
      log_debug!{ "clause_rhs_force: {}\n  {}", tterm, clause.to_string_info(& self.preds).unwrap() }
      debug_assert!( is_new )
    }
    clause.rhs = tterm
  }

  // /// Evaluates the term a predicate is forced to, if any.
  // pub fn eval_term_of(
  //   & self, pred: PrdIdx, model: & VarMap<Val>
  // ) -> Res< Option<bool> > {
  //   if let Some(term) = self.term_of(pred) {
  //     match term.bool_eval(model) {
  //       Ok(None) => bail!("partial model during predicate term evaluation"),
  //       res => res,
  //     }
  //   } else {
  //     Ok(None)
  //   }
  // }

  /// Set of int constants **appearing in the predicates**. If more constants
  /// are created after the instance building step, they will not appear here.
  pub fn consts(& self) -> & HConSet<RTerm> {
    & self.consts
  }

  /// Range over the predicate indices.
  pub fn pred_indices(& self) -> PrdRange {
    PrdRange::zero_to( self.preds.len() )
  }
  /// Range over the clause indices.
  pub fn clause_indices(& self) -> ClsRange {
    ClsRange::zero_to( self.clauses.len() )
  }

  /// Predicate accessor.
  pub fn preds(& self) -> & PrdMap<PrdInfo> {
    & self.preds
  }
  /// Clause accessor.
  pub fn clauses(& self) -> & ClsMap<Clause> {
    & self.clauses
  }

  /// Removes all predicate applications of some predicate in the lhs of a
  /// clause.
  fn rm_pred_apps_in_lhs(& mut self, pred: PrdIdx, clause: ClsIdx) {
    self.pred_to_clauses[pred].0.remove(& clause) ;
    self.clauses[clause].lhs_preds.remove(& pred) ;
  }


  /// Strengthens some predicate by some terms using the clauses lhs where the
  /// predicate appears.
  ///
  /// Returns the number of clauses created.
  ///
  /// Currently pseudo-inactive. Can only remove predicate applications if they
  /// are found to be trivial given the strengthening.
  ///
  /// For all clauses `c` where `pred` appears in the lhs, creates a new clause
  /// that is `c` with every application of `pred` replaced by `tterms`
  /// instantiated on `pred`'s application arguments.
  pub fn strengthen_in_lhs(
    & mut self, pred: PrdIdx, tterms: Vec<TTerm>
  ) -> Res<usize> {
    // let mut nu_clauses = Vec::with_capacity(
    //   self.pred_to_clauses[pred].0.len()
    // ) ;
    let mut nu_tterms = HashSet::with_capacity( 29 ) ;
    let mut pred_apps_to_rm = Vec::with_capacity(11) ;

    'clause_iter: for clause in & self.pred_to_clauses[pred].0 {
      // debug_assert!( nu_tterms.is_empty() ) ;
      nu_tterms.clear() ;

      log_debug!{ "  - #{}", clause }

      if let Some(argss) = self[* clause].lhs_preds.get(& pred) {

        log_debug!{ "    {} applications", argss.len() }
        for args in argss {
          'tterm_iter: for tterm in & tterms {
            let tterm = tterm.subst_total(args) ? ;
            if let Some(b) = tterm.bool() {
              if ! b {
                log_debug!{ "      new clause is trivial, skipping" }
                continue 'clause_iter
              }
            } else {
              match tterm {
                TTerm::T(ref term) if self[
                  * clause
                ].lhs_terms.contains(term) => continue 'tterm_iter,
                TTerm::P { ref pred, ref args } if self[
                  * clause
                ].lhs_preds.get(pred).map(
                  |argss| argss.contains(args)
                ).unwrap_or(false) => continue 'tterm_iter,
                _ => ()
              }
              log_debug!{ "    - {}", tterm }
              nu_tterms.insert( tterm ) ;
            }
          }
        }

      } else {
        bail!(
          "inconsistent instance state \
          (`pred_to_clauses` in `strengthen_in_lhs`)"
        )
      }

      if nu_tterms.is_empty() {
        log_debug!{
          "    no new terms, can remove applications of this predicate"
        }
        pred_apps_to_rm.push( (pred, * clause) )
      } else {
        // let mut nu_clause = self[* clause].clone() ;

        // for tterm in nu_tterms.drain() {
        //   nu_clause.lhs_insert(tterm) ;
        // }

        // let should_remove = self.simplifier.clause_propagate(
        //   & mut nu_clause
        // ) ? ;
        // if should_remove {
        //   log_info!{
        //     "    new clause is trivial after propagation"
        //   }
        // } else {
        //   nu_clauses.push(nu_clause)
        // }
      }

    }

    for (pred, clause) in pred_apps_to_rm {
      self.rm_pred_apps_in_lhs(pred, clause)
    }
    // let count = nu_clauses.len() ;
    // log_info!{ "    adding {} clauses", count }
    // for clause in nu_clauses { self.push_clause(clause) ? }
    self.check("after strengthening (lhs)") ? ;

    // Ok(count)
    Ok(0)
  }

  /// Pushes a new predicate and returns its index.
  pub fn push_pred(
    & mut self, name: String, sig: VarMap<Typ>
  ) -> PrdIdx {
    self.max_pred_arity = ::std::cmp::max(
      self.max_pred_arity, sig.len().into()
    ) ;
    let idx = self.preds.next_index() ;
    self.preds.push( PrdInfo { name, idx, sig } ) ;
    self.pred_terms.push(None) ;
    self.pred_qterms.push(None) ;
    self.pred_to_clauses.push(
      ( ClsSet::with_capacity(17), ClsSet::with_capacity(17) )
    ) ;
    idx
  }

  /// Forces a predicate to be equal to something.
  ///
  /// Does not impact `pred_to_clauses`.
  fn force_pred(
    & mut self, pred: PrdIdx, quals: Option<Qualfed>, tterms: TTerms
  ) -> Res<()> {
    if let Some(_) = self.pred_terms[pred].as_ref() {
      bail!(
        "[bug] trying to force predicate {} twice\n{}\n{} qualifier(s)",
        conf.sad(& self[pred].name),
        tterms, quals.map(|q| q.len()).unwrap_or(0)
      )
    }
    if let Some(_) = self.pred_qterms[pred].as_ref() {
      bail!(
        "trying to force predicate {} twice\n{}\n{} qualifier(s)",
        conf.sad(& self[pred].name),
        tterms, quals.map(|q| q.len()).unwrap_or(0)
      )
    }
    if let Some(quals) = quals {
      self.pred_qterms[pred] = Some( (quals, tterms) )
    } else {
      self.pred_terms[pred] = Some(tterms)
    }
    Ok(())
  }

  /// Unlinks a predicate from all the clauses it's linked to, and conversely.
  ///
  /// Only impacts `self.pred_to_clauses`.
  fn drain_unlink_pred(
    & mut self, pred: PrdIdx, lhs: & mut ClsSet, rhs: & mut ClsSet
  ) -> () {
    for clause in self.pred_to_clauses[pred].0.drain() {
      lhs.insert(clause) ;
    }
    for clause in self.pred_to_clauses[pred].1.drain() {
      rhs.insert(clause) ;
    }
  }

  /// Goes trough the predicates in `from`, and updates `pred_to_clauses` so
  /// that they point to `to` instead.
  fn relink_preds_to_clauses(
    & mut self, from: ClsIdx, to: ClsIdx
  ) -> Res<()> {
    for pred in self.clauses[from].lhs_preds.keys() {
      let pred = * pred ;
      let was_there = self.pred_to_clauses[pred].0.remove(& from) ;
      let _ = self.pred_to_clauses[pred].0.insert(to) ;
      debug_assert!(was_there)
    }
    if let Some(pred) = self.clauses[from].rhs().pred() {
      let was_there = self.pred_to_clauses[pred].1.remove(& from) ;
      let _ = self.pred_to_clauses[pred].1.insert(to) ;
      debug_assert!(was_there)
    }
    Ok(())
  }

  // /// Unlinks a predicate from a clause.
  // fn unlink_pred_and_clause(
  //   & mut self, pred: PrdIdx, clause: ClsIdx
  // ) -> Res<()> {
  //   let in_lhs = self.pred_to_clauses[pred].0.remove(& clause) ;
  //   let in_rhs = self.pred_to_clauses[pred].1.remove(& clause) ;
  //   if ! (in_lhs && in_rhs ) {
  //     bail!(
  //       "predicate {} is not linked to clause number {}, failed to unlink",
  //       conf.sad(& self[pred].name), clause
  //     )
  //   } else {
  //     Ok(())
  //   }
  // }

  /// Forget some clauses.
  ///
  /// Duplicates are handled as if they was only one.
  pub fn forget_clauses(& mut self, mut clauses: Vec<ClsIdx>) -> Res<()> {
    // Forgetting is done by swap remove, so we sort in DESCENDING order so
    // that indices always make sense.
    clauses.sort_unstable_by(
      |c_1, c_2| c_2.cmp(c_1)
    ) ;
    let mut prev = None ;
    for clause in clauses {
      log_debug!{ "forgetting {}", self[clause].to_string_info(& self.preds) ? }
      if prev == Some(clause) { continue }
      prev = Some(clause) ;
      let _ = self.forget_clause(clause) ? ;
    }
    self.check("after `forget_clause`") ? ;
    Ok(())
  }

  /// Forget a clause. **Does not preserve the order of the clauses.**
  ///
  /// Also unlinks predicates from `pred_to_clauses`.
  pub fn forget_clause(& mut self, clause: ClsIdx) -> Res<Clause> {
    for pred in self.clauses[clause].lhs_preds.keys() {
      let pred = * pred ;
      let was_there = self.pred_to_clauses[pred].0.remove(& clause) ;
      debug_assert!(
        was_there || self.pred_terms[pred].is_some()
      )
    }
    if let TTerm::P { pred, .. } = * self.clauses[clause].rhs() {
      let was_there = self.pred_to_clauses[pred].1.remove(& clause) ;
      debug_assert!(
        was_there || self.pred_terms[pred].is_some()
      )
    }
    // Relink the last clause as its index is going to be `clause`. Except if
    // `clause` is already the last one.
    let last_clause: ClsIdx = ( self.clauses.len() - 1 ).into() ;
    if clause != last_clause {
      self.relink_preds_to_clauses(last_clause, clause) ?
    } else {
      log_info!{ "  last clause" }
    }
    let res = self.clauses.swap_remove(clause) ;
    Ok(res)
  }

  /// Pushes a new clause.
  pub fn push_clause(& mut self, clause: Clause) -> Res<()> {
    let clause_index = self.clauses.next_index() ;
    for pred in clause.lhs_preds.keys() {
      let pred = * pred ;
      let is_new = self.pred_to_clauses[pred].0.insert(clause_index) ;
      debug_assert!(is_new)
    }
    if let Some(pred) = clause.rhs.pred() {
      let is_new = self.pred_to_clauses[pred].1.insert(clause_index) ;
      debug_assert!(is_new)
    }
    self.clauses.push(clause) ;
    self.check("after `push_clause`")
  }


  /// Simplifies a cause. Returns `true` if the clause was (swap) removed.
  pub fn simplify_clause(& mut self, clause: ClsIdx) -> Res<bool> {
    let remove = self.simplifier.clause_propagate(
      & mut self.clauses[clause]
    ).chain_err(
      || format!(
        "on clause {}",
        self.clauses[clause].to_string_info(& self.preds).unwrap()
      )
    ) ? ;
    if remove {
      self.forget_clause(clause) ? ;
    }
    Ok(remove)
  }



  /// Simplifies the clauses. Returns the number of clauses removed.
  ///
  /// - propagates variable equalities in clauses' lhs
  ///
  /// # TO DO
  ///
  /// - currently kind of assumes equalities are binary, fix?
  pub fn simplify_clauses(& mut self) -> Res<RedInfo> {
    let mut changed = true ;
    let mut red_info: RedInfo = (0, 0, 0).into() ;
    let mut nu_clauses = Vec::with_capacity(7) ;
    while changed {
      changed = false ;

      let mut clause: ClsIdx = 0.into() ;
      while clause < self.clauses.len() {
        let removed = self.simplify_clause(clause) ? ;
        if ! removed {
          clause.inc()
        } else {
          red_info.clauses_rmed += 1
        }
      }

      // Split disjunctions.
      'find_clause: for clause in self.clauses.iter_mut() {
        // Skip those for which the predicate in the rhs only appears in this
        // rhs.
        if let Some(pred) = clause.rhs.pred() {
          if self.pred_to_clauses[pred].1.len() == 1 {
            continue 'find_clause
          }
        }

        // Skip if clause contains more than 2 disjunctions.
        let mut disj = None ;
        let mut disj_count = 0 ;
        for term in & clause.lhs_terms {
          if let Some(args) = term.disj_inspect() {
            disj_count += 1 ;
            if disj.is_none() {
              disj = Some((term.clone(), args.clone()))
            }
          }
        }
        if disj_count > 2 {
          continue 'find_clause
        }
        if let Some((disj, mut kids)) = disj {
          log_debug!{
            "splitting clause {}", clause.to_string_info(& self.preds) ?
          }
          let _was_there = clause.lhs_terms.remove(& disj) ;
          debug_assert!(_was_there) ;
          if let Some(kid) = kids.pop() {
            for kid in kids {
              let mut clause = clause.clone() ;
              clause.insert_term(kid) ;
              nu_clauses.push(clause)
            }
            clause.insert_term(kid) ;
          } else {
            bail!("illegal empty disjunction")
          }
        }
      }

      if ! nu_clauses.is_empty() {
        changed = true ;
        red_info.clauses_added += nu_clauses.len() ;
        for clause in nu_clauses.drain(0..) {
          self.push_clause(clause) ?
        }
      }

      self.check("during clause simplification") ?
    }


    Ok(red_info)
  }

  /// Extracts some qualifiers from all clauses.
  pub fn qualifiers(& self, quals: & mut Quals) {
    for clause in & self.clauses {
      // println!("  - mining clause\n{}", clause.to_string_info(& self.preds).unwrap()) ;
      self.qualifiers_of_clause(clause, quals)
    }
  }

  /// Extracts some qualifiers from a clause.
  ///
  /// # TO DO
  ///
  /// - write an explanation of what actually happens
  /// - and some tests, probably
  pub fn qualifiers_of_clause(
    & self, clause: & Clause, quals: & mut Quals
  ) {

    // println!(
    //   "qualifiers for clause {}", clause.to_string_info(& self.preds).unwrap()
    // ) ;

    // Extraction of the variables map based on the way the predicates are
    // used.
    let mut maps = vec![] ;

    // Qualifiers generated while looking at predicate applications.
    let mut app_quals = HConSet::with_capacity(17) ;

    let rhs_opt = if let TTerm::P { ref pred, ref args } = clause.rhs {
      let mut set = VarMapSet::with_capacity(1) ;
      set.insert(args.clone()) ;
      Some((pred, set))
    } else { None } ;

    {
      // Represents equalities between *pred vars* and terms over *clause
      // variables*. These will be added to `app_quals` if the total
      // substitution of the term by `map` succeeds.
      let mut eq_quals = VarHMap::with_capacity(7) ;

      let rhs_opt = rhs_opt.as_ref().map( |& (pred, ref set)| (pred, set) ) ;

      for (_, argss) in clause.lhs_preds.iter().chain( rhs_opt.into_iter() ) {
        debug_assert!( app_quals.is_empty() ) ;
        for args in argss {
          debug_assert!( eq_quals.is_empty() ) ;

          // All the *clause var* to *pred var* maps for this predicate
          // application.
          let mut map: VarHMap<Term> = VarHMap::with_capacity( args.len() ) ;

          // println!("  iterating over pred app") ;
          for (pred_var, term) in args.index_iter() {
            // println!("v_{}: {}", pred_var, term) ;

            // Parameter's a variable?
            if let Some(clause_var_index) = term.var_idx() {

              // Clause variable's already known as parameter?
              if let Some(other_pred_var) = map.get(& clause_var_index).map(
                |t| t.clone()
              ) {
                // Equality qualifier.
                app_quals.insert(
                  term::eq( term::var(pred_var), other_pred_var.clone() )
                ) ;
              } else {
                // Add to map.
                let _prev = map.insert(clause_var_index, term::var(pred_var)) ;
                debug_assert!( _prev.is_none() )
              }

            } else {
              // Parameter's not a variable, store potential equality.
              let _prev = eq_quals.insert(pred_var, term) ;
              debug_assert!( _prev.is_none() )
            }

          }

          // println!("  generating var / term equalities") ;
          for (pred, term) in eq_quals.drain() {
            if let Some((term, _)) = term.subst_total(& map) {
              app_quals.insert( term::eq( term::var(pred), term ) ) ;
            }
          }

          if ! app_quals.is_empty() {
            let mut highest_var: VarIdx = 0.into() ;
            let build_conj = app_quals.len() > 1 ;
            let mut conj = Vec::with_capacity( app_quals.len() ) ;
            for term in app_quals.drain() {
              if let Some(max_var) = term.highest_var() {
                if build_conj { conj.push(term.clone()) }
                let arity: Arity = (1 + * max_var).into() ;
                // println!("- {}", term) ;
                quals.insert(arity, term) ;
                if max_var > highest_var { highest_var = max_var }
              } else {
                // Unreachable because all the elements of `app_quals` are
                // equalities between a variable and something else.
                unreachable!()
              }
            }
            if build_conj {
              let term = term::and(conj) ;
              // println!("- {}", term) ;
              quals.insert( (1 + * highest_var).into(), term )
            }
          }

          maps.push(map)
        }
      }
    }

    // Build the conjunction of atoms.
    let mut conjs = vec![
      ( HConSet::with_capacity( clause.lhs_terms.len() + 1 ), 0.into() ) ;
      maps.len()
    ] ;

    let rhs = clause.rhs().term() ;
    // Now look for atoms and try to apply the mappings above.
    for term in clause.lhs_terms.iter().chain( clause.rhs().term() ) {
      let push = rhs.is_none() || rhs == Some(& term) ;

      let mut cnt = 0 ;
      for map in & maps {
        if let Some( (term, true) ) = term.subst_total(map) {
          if let Some(max_var) = term.highest_var() {
            let arity: Arity = (1 + * max_var).into() ;
            if push {
              conjs[cnt].0.insert( term.clone() ) ;
              if arity > conjs[cnt].1 { conjs[cnt].1 = arity }
            }
            cnt += 1 ;
            let term = if let Some(term) = term.rm_neg() {
              term
            } else { term } ;
            // println!("- {}", term) ;
            quals.insert(arity, term)
          }
        }
      }

    }

    for (conj, max_arity) in conjs {
      if conj.len() > 1 {
        let term = term::and( conj.into_iter().collect() ) ;
        // println!("- {}", term) ;
        quals.insert( max_arity, term )
      }
    }

  }

  /// Turns a teacher counterexample into learning data.
  pub fn cexs_to_data(
    & self, data: & mut ::common::data::Data, cexs: Cexs
  ) -> Res<bool> {
    let mut nu_stuff = false ;
    for (clause, cex) in cexs.into_iter() {
      log_debug!{ "    working on clause {}...", clause }
      let clause = & self[clause] ;
      log_debug!{ "    getting antecedents..." }
      let mut antecedents = Vec::with_capacity( clause.lhs_len() ) ;
      log_debug!{ "    translating tterms..." }


      log_debug!{ "    working on lhs..." }
      for (pred, argss) in & clause.lhs_preds {
        let pred = * pred ;
        log_debug!{
          "        pred: {} / {} ({})",
          pred, self.preds.len(), self.pred_terms.len()
        }
        if self.pred_terms[pred].is_none() {
          log_debug!{ "        -> is none, {} args", argss.len() }
          for args in argss {
            let mut values = VarMap::with_capacity( args.len() ) ;
            for arg in args {
              values.push(
                arg.eval(& cex).chain_err(
                  || "during argument evaluation to generate learning data"
                ) ?
              )
            }
            antecedents.push(
              (pred, values)
            )
          }
        } else {
          log_debug!{ "      -> is some" }
        }
      }
      antecedents.shrink_to_fit() ;
      
      log_debug!{ "    working on rhs..." }
      let consequent = match * clause.rhs() {
        TTerm::P { pred, ref args } => {
          log_debug!{
            "        pred: {} / {} ({})",
            pred, self.preds.len(), self.pred_terms.len()
          }
          let mut values = VarMap::with_capacity( args.len() ) ;
          'pred_args: for arg in args {
            values.push(
              arg.eval(& cex).chain_err(
                || "during argument evaluation to generate learning data"
              ) ?
            )
          }
          Some( (pred, values) )
        },
        _ => None,
      } ;

      log_debug!{ "    antecedent: {:?}", antecedents }
      log_debug!{ "    consequent: {:?}", consequent }

      match ( antecedents.len(), consequent ) {
        (0, None) => bail!(
          "[unimplemented] clause with no predicate has a cex (unsafe)"
        ),
        (1, None) => {
          let (pred, args) = antecedents.pop().unwrap() ;
          let new = data.stage_raw_neg(pred, args) ? ;
          nu_stuff = nu_stuff || new
        },
        (0, Some( (pred, args) )) => {
          let new = data.stage_raw_pos(pred, args) ? ;
          nu_stuff = nu_stuff || new
        },
        (_, consequent) => {
          let new = data.add_cstr(antecedents, consequent) ? ;
          nu_stuff = nu_stuff || new
        },
      }
    }

    Ok(nu_stuff)
  }



  /// Checks that the instance has no inconsistencies.
  ///
  /// Only active in debug.
  #[cfg(not(debug_assertions))]
  #[inline(always)]
  pub fn check(& self, _: & 'static str) -> Res<()> { Ok(()) }

  #[cfg(debug_assertions)]
  pub fn check(& self, s: & 'static str) -> Res<()> {
    self.check_pred_to_clauses().chain_err(
      || format!("while checking `{}`", conf.sad("pred_to_clauses"))
    ).chain_err(
      || format!("instance consistency check failed: {}", conf.emph(s))
    ) ? ;

    Ok(())
  }

  /// Pretty printer for a set of clauses.
  #[cfg(debug_assertions)]
  fn pretty_clauses(& self, clauses: & ClsSet) -> String {
    let mut s = String::new() ;
    s.push('{') ;
    for clause in clauses {
      s.push(' ') ;
      s.push_str(& format!("{}", clause))
    }
    s.push(' ') ;
    s.push('}') ;
    s
  }

  /// Checks the consistency of `pred_to_clauses`.
  #[cfg(debug_assertions)]
  fn check_pred_to_clauses(& self) -> Res<()> {
    for (cls_idx, clause) in self.clauses.index_iter() {
      for (pred, _) in & clause.lhs_preds {
        let pred = * pred ;
        if ! self.pred_to_clauses[pred].0.contains(& cls_idx) {
          bail!(
            "predicate {} appears in lhs of clause {} \
            but is not registered as such\n{}\nlhs: {}\nrhs: {}",
            self[pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_clauses(
              & self.pred_to_clauses[pred].0
            ), self.pretty_clauses(
              & self.pred_to_clauses[pred].1
            )
          )
        }
      }
      if let Some(pred) = clause.rhs.pred() {
        if ! self.pred_to_clauses[pred].1.contains(& cls_idx) {
          bail!(
            "predicate {} appears in rhs of clause {} \
            but is not registered as such\n{}\nlhs: {}\nrhs: {}",
            self[pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_clauses(
              & self.pred_to_clauses[pred].0
            ), self.pretty_clauses(
              & self.pred_to_clauses[pred].1
            )
          )
        }
      }
    }

    for (pred, & (ref lhs, ref rhs)) in self.pred_to_clauses.index_iter() {
      'pred_clauses: for clause in lhs {
        if * clause >= self.clauses.len() {
          bail!(
            "predicate {} is registered as appearing in lhs of clause {} \
            which is above the maximal clause index", self[pred], clause
          )
        }
        if self.clauses[* clause].lhs_preds.get(& pred).is_none() {
          bail!(
            "predicate {} is registered as appearing in lhs of clause {} \
            but it's not the case\n{}\nlhs: {}\nrhs: {}",
            self[pred], clause,
            self.clauses[* clause].to_string_info(self.preds()) ?,
            self.pretty_clauses(
              & self.pred_to_clauses[pred].0
            ), self.pretty_clauses(
              & self.pred_to_clauses[pred].1
            )
          )
        }
      }
      for clause in rhs {
        if * clause >= self.clauses.len() {
          bail!(
            "predicate {} is registered as appearing in rhs of clause {} \
            which is above the maximal clause index", self[pred], clause
          )
        }
        if let Some(this_pred) = self.clauses[* clause].rhs.pred() {
          if this_pred == pred {
            continue
          }
        }
        bail!(
          "predicate {} is registered to appear in rhs of clause {} \
          but it's not the case\n{}\nlhs: {}\nrhs: {}",
          self[pred], clause,
          self.clauses[* clause].to_string_info(self.preds()) ?,
          self.pretty_clauses(
            & self.pred_to_clauses[pred].0
          ), self.pretty_clauses(
            & self.pred_to_clauses[pred].1
          )
        )
      }
    }
    Ok(())
  }


  /// Forces some predicates to false. Returns the number of clauses dropped.
  pub fn force_false<Preds: IntoIterator<Item = PrdIdx>>(
    & mut self, preds: Preds
  ) -> Res<RedInfo> {
    let mut res = self.internal_force_false(preds) ? ;
    if res.non_zero() { res += self.force_trivial() ? }
    Ok(res)
  }
  /// Forces some predicates to false. Returns the number of clauses dropped.
  ///
  /// Internal version, does not call `force_trivial`.
  fn internal_force_false<Preds: IntoIterator<Item = PrdIdx>>(
    & mut self, preds: Preds
  ) -> Res<RedInfo> {
    self.check("before force false") ? ;
    let mut clauses_dropped = 0 ;
    let (mut clause_lhs, mut clause_rhs) = (ClsSet::new(), ClsSet::new()) ;
    let fls = TTerms::fls() ;
    for pred in preds.into_iter() {
      debug_assert!( clause_lhs.is_empty() ) ;
      debug_assert!( clause_rhs.is_empty() ) ;

      self.force_pred( pred, None, fls.clone() ) ? ;
      self.drain_unlink_pred(pred, & mut clause_lhs, & mut clause_rhs) ;

      clauses_dropped += clause_lhs.len() ;
      for clause in clause_rhs.drain() {
        debug_assert_eq!{ self.clauses[clause].rhs.pred(), Some(pred) }
        self.clauses[clause].rhs = TTerm::T( term::fls() )
      }
      debug_assert!{{
        for clause in & clause_lhs {
          debug_assert!( self[*clause].lhs_preds().get(& pred).is_some() )
        }
        true
      }}
      self.forget_clauses( clause_lhs.drain().collect() ) ?
    }
    self.check("force_false") ? ;
    Ok( (0, clauses_dropped, 0).into() )
  }



  /// Forces some predicates to false. Returns the number of clauses dropped.
  pub fn force_true<Preds: IntoIterator<Item = PrdIdx>>(
    & mut self, preds: Preds
  ) -> Res<RedInfo> {
    let mut res = self.internal_force_true(preds) ? ;
    if res.non_zero() { res += self.force_trivial() ? }
    Ok(res)
  }
  /// Forces some predicates to true.
  ///
  /// Internal version, does not call `force_trivial`.
  fn internal_force_true<Preds: IntoIterator<Item = PrdIdx>>(
    & mut self, preds: Preds
  ) -> Res<RedInfo> {
    let mut clauses_dropped = 0 ;
    let (mut clause_lhs, mut clause_rhs) = (ClsSet::new(), ClsSet::new()) ;
    let tru = TTerms::tru() ;
    
    for pred in preds.into_iter() {
      debug_assert!( clause_lhs.is_empty() ) ;
      debug_assert!( clause_rhs.is_empty() ) ;

      self.force_pred( pred, None, tru.clone() ) ? ;
      self.drain_unlink_pred(pred, & mut clause_lhs, & mut clause_rhs) ;

      for clause in clause_lhs.drain() {
        self.clauses[clause].lhs_preds.remove(& pred) ;
      }
      clauses_dropped += clause_rhs.len() ;
      self.forget_clauses( clause_rhs.drain().collect() ) ? ;
    }
    self.check("force_true") ? ;
    Ok( (0, clauses_dropped, 0).into() )
  }




  /// Forces to false (true) all the predicates that only appear in clauses'
  /// lhs (rhs).
  pub fn force_trivial( & mut self) -> Res< RedInfo > {
    let mut info: RedInfo = (0, 0, 0).into() ;
    let mut fixed_point = false ;
    while ! fixed_point {
      fixed_point = true ;
      for pred in PrdRange::zero_to( self.preds.len() ) {
        if ! self.is_known(pred) {
          if self.pred_to_clauses[pred].1.is_empty() {
            info.preds += 1 ;
            fixed_point = false ;
            info += self.internal_force_false( Some(pred) ) ?
          } else if self.pred_to_clauses[pred].0.is_empty() {
            info.preds += 1 ;
            fixed_point = false ;
            info += self.internal_force_true( Some(pred) ) ?
          }
        }
      }
    }
    Ok(info)
  }




  /// Forces some predicates to be something.
  pub fn force_preds<Preds: IntoIterator<
    Item = (PrdIdx, Option<Qualfed>, TTerms)
  >>(
    & mut self, preds: Preds
  ) -> Res<RedInfo> {
    let (mut clause_lhs, mut clause_rhs) = (ClsSet::new(), ClsSet::new()) ;
    // let mut terms_to_add = vec![] ;
    let mut clauses_to_rm = ClsSet::new() ;
    let mut clauses_rmed = 0 ;
    // We need to add clauses when forcing a predicate to be a disjunction.
    let mut clauses_to_add = Vec::with_capacity(10) ;
    let mut clauses_added = 0 ;

    log_debug!{ "  force preds..." }

    for (pred, quals, tterms) in preds.into_iter() {
      debug_assert!( clause_lhs.is_empty() ) ;
      debug_assert!( clause_rhs.is_empty() ) ;
      debug_assert!( clauses_to_add.is_empty() ) ;
      debug_assert!( clauses_to_rm.is_empty() ) ;
      
      log_debug!{ "  - {}", self[pred] }

      self.drain_unlink_pred(pred, & mut clause_lhs, & mut clause_rhs) ;

      {
        let quals = quals.as_ref() ;

        // LHS.
        'clause_iter_lhs: for clause in clause_lhs.drain() {
          // debug_assert!( terms_to_add.is_empty() ) ;
          
          if clauses_to_rm.contains(& clause) { continue 'clause_iter_lhs }

          log_debug!{ "    working on lhs of clause #{}", clause }

          if let Some(argss) = self.clauses[clause].lhs_preds.remove(& pred) {
            for args in argss {

              match if let Some(quals) = quals {
                let qual_map = self.clauses[clause].fresh_vars_for(quals) ;
                tterms.subst_total( & (& args, qual_map) ) ?
              } else {
                tterms.subst_total(& args) ?
              } {
                TTerms::True => (),
                TTerms::False => {
                  // terms_to_add.clear() ;
                  clauses_to_rm.insert(clause) ;
                  continue 'clause_iter_lhs
                },
                TTerms::And(tterms) => {
                  // log_debug!{ "    extending..." }
                  // for tterm in & tterms {
                  //   log_debug!{ "    - {}", tterm }
                  // }
                  self.clause_lhs_extend(clause, tterms)
                },
                TTerms::Or(mut _tterms) => {
                  unimplemented!("disjunction of top terms in `force_preds`")
                },
              }
            }
          } else {
            bail!(
              "inconsistent instance state, \
              `pred_to_clauses` and clauses out of sync"
            )
          }

          // self.clauses[clause].lhs.extend( terms_to_add.drain(0..) ) ;

          log_debug!{ "forced pred in a clause: {}", self.clauses[clause].to_string_info(& self.preds).unwrap() }

          let remove = self.simplifier.clause_propagate(
            & mut self.clauses[clause]
          ).chain_err(
            || format!(
              "on clause {}",
              self.clauses[clause].to_string_info(& self.preds).unwrap()
            )
          ) ? ;
          if remove { clauses_to_rm.insert(clause) ; () }

        }
      }

      if quals.is_some() {
        debug_assert!( clause_rhs.is_empty() )
      } else {

        // RHS.
        'clause_iter_rhs: for clause in clause_rhs.drain() {
          log_debug!{ "    rhs of #{}...", clause }

          if clauses_to_rm.contains(& clause) { continue 'clause_iter_rhs }

          // debug_assert!( terms_to_add.is_empty() ) ;

          let tterms = if let TTerm::P {
            pred: _this_pred, ref args
          } = self[clause].rhs {
            debug_assert_eq!( _this_pred, pred ) ;
            tterms.subst_total(args) ?
          } else {
            bail!("inconsistent instance")
          } ;

          match tterms {
            TTerms::True => {
              clauses_to_rm.insert(clause) ;
              continue 'clause_iter_rhs
            },
            TTerms::False => {
              self.clauses[clause].rhs = TTerm::T( term::fls() )
            },
            TTerms::And(tterms) => {
              debug_assert!( ! tterms.is_empty() ) ;
              let mut tterms = tterms.into_iter() ;
              while let Some(tterm) = tterms.next() {
                match tterm.bool() {
                  Some(true) => {
                    clauses_to_rm.insert(clause) ;
                  },
                  Some(false) => {
                    self.clause_rhs_force(
                      clause, TTerm::T( term::fls() )
                    ) ;
                    break
                  },
                  None => {
                    self.clause_rhs_force(
                      clause, tterm
                    ) ;
                    break
                  },
                }
              }
              for tterm in tterms {
                let tterm = match tterm.bool() {
                  Some(true) => continue,
                  Some(false) => TTerm::T( term::fls() ),
                  None => tterm,
                } ;
                let clause = self.clauses[clause].clone_with_rhs(tterm) ;
                clauses_to_add.push(clause)
                // self.push_clause(clause) ?
              }
            },
            TTerms::Or(_) => bail!(
              "trying to force a rhs to a dnf"
            ),
          }

        }

      }

      if ! tterms.mention_pred(pred) {
        log_debug!{ "    forcing {}", self[pred] }
        self.force_pred(pred, quals, tterms) ?
      }
      clauses_rmed += clauses_to_rm.len() ;
      self.forget_clauses( clauses_to_rm.drain().collect() ) ? ;
      clauses_added += clauses_to_add.len() ;
      for clause in clauses_to_add.drain(0..) {
        self.push_clause(clause) ?
      }
    }

    let mut info: RedInfo = (0, clauses_rmed, clauses_added).into() ;
    info += self.force_trivial() ? ;
    info += self.simplify_clauses() ? ;
    Ok( info )
  }

  /// Dumps the instance as an SMT-LIB 2 problem.
  pub fn dump_as_smt2<File, Blah>(
    & self, w: & mut File, blah: Blah
  ) -> Res<()>
  where File: Write, Blah: AsRef<str> {
    use common::consts::keywords ;
    let blah = blah.as_ref() ;

    for line in blah.lines() {
      write!(w, "; {}\n", line) ?
    }
    write!(w, "\n") ? ;

    for (pred_idx, pred) in self.preds.index_iter() {
      if self.pred_terms[pred_idx].is_none()
      && self.pred_qterms[pred_idx].is_none() {
        write!(
          w, "({}\n  {}\n  (", keywords::prd_dec, pred.name
        ) ? ;
        for typ in & pred.sig {
          write!(w, " {}", typ) ?
        }
        write!(w, " ) Bool\n)\n") ?
      }
    }

    for (idx, clause) in self.clauses.index_iter() {
      write!(w, "\n; Clause #{}\n", idx) ? ;
      clause.write(
        w, |w, p, args| {
          write!(w, "(") ? ;
          w.write_all( self[p].name.as_bytes() ) ? ;
          for arg in args {
            write!(w, " ") ? ;
            arg.write(w, |w, var| w.write_all( clause.vars[var].as_bytes() )) ?
          }
          write!(w, ")")
        }
      ) ? ;
      write!(w, "\n\n") ?
    }

    write!(w, "\n(check-sat)\n") ? ;

    Ok(())
  }

  /// Writes a model.
  pub fn write_model<W: Write>(& self, model: & Model, w: & mut W) -> Res<()> {
    writeln!(w, "(model") ? ;
    for & (ref pred, ref qvars, ref tterms) in model {
      let pred_info = & self[* pred] ;
      writeln!(
        w, "  ({} {}", ::common::consts::keywords::prd_def, pred_info.name
      ) ? ;
      write!(w, "    (")  ?;
      for (var, typ) in pred_info.sig.index_iter() {
        write!(w, " ({} {})", term::var(var), typ) ?
      }
      writeln!(w, " ) {}", Typ::Bool) ? ;
      let (ident, closing) = if let Some(ref qvars) = * qvars {
        writeln!(w, "    (exists") ? ;
        writeln!(w, "      (") ? ;
        for (var, typ) in qvars {
          write!(w, " ({} {})", var.default_str(), typ) ?
        }
        writeln!(w, " )") ? ;
        ("      ", "\n    )")
      } else {
        ("    ", "")
      } ;
      write!(w, "{}", ident) ? ;
      self.print_tterms_as_model(w, tterms) ? ;
      writeln!(w, "{}\n  )", closing) ?
    }
    writeln!(w, ")") ? ;
    Ok(())
  }
}
impl ::std::ops::Index<ClsIdx> for Instance {
  type Output = Clause ;
  fn index(& self, index: ClsIdx) -> & Clause {
    & self.clauses[index]
  }
}
impl ::std::ops::Index<PrdIdx> for Instance {
  type Output = PrdInfo ;
  fn index(& self, index: PrdIdx) -> & PrdInfo {
    & self.preds[index]
  }
}








// impl<'a> PebcakFmt<'a> for TTerm {
//   type Info = (& 'a VarMap<VarInfo>, & 'a PrdMap<PrdInfo>) ;
//   fn pebcak_err(& self) -> ErrorKind {
//     "during top term pebcak formatting".into()
//   }
//   fn pebcak_io_fmt<W: Write>(
//     & self, w: & mut W,
//     (vars, prds): (& 'a VarMap<VarInfo>, & 'a PrdMap<PrdInfo>)
//   ) -> IoRes<()> {
//     self.write(
//       w,
//       |w, var| w.write_all( vars[var].as_bytes() ),
//       |w, prd| w.write_all( prds[prd].as_bytes() )
//     )
//   }
// }

impl<'a> PebcakFmt<'a> for Clause {
  type Info = & 'a PrdMap<PrdInfo> ;
  fn pebcak_err(& self) -> ErrorKind {
    "during clause pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, prds: & 'a PrdMap<PrdInfo>
  ) -> IoRes<()> {
    self.write(
      w, |w, prd, args| {
        write!(w, "(") ? ;
        w.write_all( prds[prd].as_bytes() ) ? ;
        for arg in args {
          write!(w, " ") ? ;
          arg.write(w, |w, var| w.write_all( self.vars[var].as_bytes() )) ?
        }
        write!(w, ")")
      }
    )
  }
}

impl<'a> PebcakFmt<'a> for Instance {
  type Info = () ;
  fn pebcak_err(& self) -> ErrorKind {
    "during instance pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, _: ()
  ) -> IoRes<()> {
    use common::consts::keywords ;

    for (pred_idx, pred) in self.preds.index_iter() {
      if self.pred_terms[pred_idx].is_none()
      && self.pred_qterms[pred_idx].is_none() {
        write!(
          w, "({}\n  {}\n  (", keywords::prd_dec, pred.name
        ) ? ;
        for typ in & pred.sig {
          write!(w, " {}", typ) ?
        }
        write!(w, " ) Bool\n)\n") ?
      }
    }

    use rsmt2::to_smt::Expr2Smt ;
    let empty_prd_set = PrdSet::new() ;
    if self.sorted_pred_terms.is_empty() {
      // Either there's no forced predicate, or we are printing before
      // finalizing.
      for (pred, & (ref quals, ref tterms)) in self.pred_qterms.index_iter().filter_map(
        |(pred, tterms_opt)| tterms_opt.as_ref().map(|tt| (pred, tt))
      ) {
        write!(w, "({} {}\n  (", keywords::prd_def, self[pred]) ? ;
        for (var, typ) in self[pred].sig.index_iter() {
          write!(w, " (v_{} {})", var, typ) ?
        }
        write!(w, " ) Bool\n") ? ;
        write!(w, "  (exists (") ? ;
        for (var, typ) in quals {
          write!(w, " ({} {})", var.default_str(), typ) ?
        }
        write!(w, " )\n    ") ? ;
        tterms.expr_to_smt2(
          w, & (& empty_prd_set, & empty_prd_set, & self.preds)
        ).unwrap() ;
        write!(w,"  )\n)\n") ?
      }
      for (pred, tterms) in self.pred_terms.index_iter().filter_map(
        |(pred, tterms_opt)| tterms_opt.as_ref().map(|tt| (pred, tt))
      ) {
        write!(w, "({} {}\n  (", keywords::prd_def, self[pred]) ? ;
        for (var, typ) in self[pred].sig.index_iter() {
          write!(w, " (v_{} {})", var, typ) ?
        }
        write!(w, " ) Bool\n  ") ? ;
        tterms.expr_to_smt2(
          w, & (& empty_prd_set, & empty_prd_set, & self.preds)
        ).unwrap() ;
        write!(w, "\n)\n") ?
      }
    } else {
      for pred in & self.sorted_pred_terms {
        write!(w, "({} {}\n  (", keywords::prd_def, self[* pred]) ? ;
        for (var, typ) in self[* pred].sig.index_iter() {
          write!(w, " (v_{} {})", var, typ) ?
        }
        let tterms = self.pred_terms[* pred].as_ref().unwrap() ;
        write!(w, " ) Bool\n  ") ? ;
        tterms.expr_to_smt2(
          w, & (& empty_prd_set, & empty_prd_set, & self.preds)
        ).unwrap() ;
        write!(w, "\n)\n", ) ?
      }
    }

    for (idx, clause) in self.clauses.index_iter() {
      write!(w, "\n; Clause #{}\n", idx) ? ;
      clause.pebcak_io_fmt(w, & self.preds) ?
    }

    write!(w, "\npred to clauses:\n") ? ;
    for (pred, & (ref lhs, ref rhs)) in self.pred_to_clauses.index_iter() {
      write!(w, "  {}: lhs {{", self[pred]) ? ;
      for lhs in lhs {
        write!(w, " {}", lhs) ?
      }
      write!(w, " }}, rhs {{") ? ;
      for rhs in rhs {
        write!(w, " {}", rhs) ?
      }
      write!(w, " }}\n") ?
    }

    Ok(())
  }
}

/// Simplifies clauses.
///
/// The goal of this type is to avoid reallocation and compartment the clause
/// simplification process.
struct ClauseSimplifier {
  /// Maps variables to their representative.
  var_to_rep: VarHMap<VarIdx>,
  /// Maps variables to their representative as a term.
  var_to_rep_term: VarHMap<Term>,
  /// Maps representatives to their equivalence set.
  rep_to_vars: VarHMap<VarSet>,
  /// Maps representatives to a term they're equal to according to an equality
  /// in the clause's lhs.
  rep_to_term: VarHMap<Term>,
  /// Mpas representatives to the final term they're equal to.
  rep_to_stable_term: VarHMap<Term>,
  /// Terms to add to the clause.
  terms_to_add: Vec<Term>,
  /// Stores equalities found in clauses.
  eqs: Vec<Term>,
}
impl ClauseSimplifier {
  /// Constructor.
  pub fn new() -> Self {
    ClauseSimplifier {
      var_to_rep: VarHMap::with_capacity(29),
      var_to_rep_term: VarHMap::with_capacity(29),
      rep_to_vars: VarHMap::with_capacity(29),
      rep_to_term: VarHMap::with_capacity(29),
      rep_to_stable_term: VarHMap::with_capacity(29),
      terms_to_add: Vec::with_capacity(29),
      eqs: Vec::with_capacity(11),
    }
  }

  /// Prints its state.
  #[cfg( not(feature = "bench") )]
  #[allow(dead_code)]
  fn print_state(& self, pref: & str) {
    if ! self.var_to_rep.is_empty() {
      log_debug!{ "{}var_to_rep {{", pref }
      for (var, rep) in & self.var_to_rep {
        log_debug!{ "{}  {} -> {}", pref, var, rep }
      }
      log_debug!{ "{}}}", pref }
    }
    if ! self.var_to_rep_term.is_empty() {
      log_debug!{ "{}var_to_rep_term {{", pref }
      for (var, rep) in & self.var_to_rep_term {
        log_debug!{ "{}  {} -> {}", pref, var, rep }
      }
      log_debug!{ "{}}}", pref }
    }
    if ! self.rep_to_vars.is_empty() {
      log_debug!{ "{}rep_to_vars {{", pref }
      for (rep, set) in & self.rep_to_vars {
        log_debug!{ "{}  {} -> {}", pref, rep, Self::pretty_varset(set) }
      }
      log_debug!{ "{}}}", pref }
    }
    if ! self.rep_to_term.is_empty() {
      log_debug!{ "{}rep_to_term {{", pref }
      for (rep, term) in & self.rep_to_term {
        log_debug!{ "{}  {} -> {}", pref, rep, term }
      }
      log_debug!{ "{}}}", pref }
    }
    if ! self.rep_to_stable_term.is_empty() {
      log_debug!{ "{}rep_to_stable_term {{", pref }
      for (rep, term) in & self.rep_to_stable_term {
        log_debug!{ "{}  {} -> {}", pref, rep, term }
      }
      log_debug!{ "{}}}", pref }
    }
    if ! self.terms_to_add.is_empty() {
      log_debug!{ "{}terms_to_add {{", pref }
      for term in & self.terms_to_add {
        log_debug!{ "{}  {}", pref, term }
      }
      log_debug!{ "{}}}", pref }
    }
  }

  /// Pretty printer set of variables.
  #[cfg( not(feature = "bench") )]
  #[allow(dead_code)]
  fn pretty_varset(set: & VarSet) -> String {
    let mut s = String::new() ;
    s.push('{') ;
    for var in set {
      s.push_str( & format!(" {}", var) )
    }
    s.push(' ') ;
    s.push('}') ;
    s
  }

  /// Checks internal consistency.
  #[cfg(debug_assertions)]
  fn check(& self, vars: & VarMap<VarInfo>) -> Res<()> {
    // Representatives can only be mapped to themselves.
    for (var, rep) in & self.var_to_rep {
      if var != rep {
        for (_, rep) in & self.var_to_rep {
          if var == rep {
            bail!(
              "representative {} is mapped to representative {}",
              vars[* var], vars[* rep]
            )
          }
        }
      }
    }
    // Make sure `var_to_rep` and `rep_to_vars` are consistent.
    for (var, rep) in & self.var_to_rep {
      if var != rep {
        if ! self.rep_to_vars.get(rep).map(
          |set| set.contains(var)
        ).unwrap_or(false) {
          bail!{
            "{} is mapped to representative {}, \
            but does not appear in its equivalence class",
            vars[* var], vars[* rep]
          }
        }
      }
    }
    for (rep, set) in & self.rep_to_vars {
      for var in set {
        if self.var_to_rep.get(var) != Some(rep) {
          bail!{
            "{} is in the equivalence class of {} but is not mapped to it",
            vars[* var], vars[* rep]
          }
        }
      }
    }
    Ok(())
  }
  #[cfg( not(debug_assertions) )]
  #[inline(always)]
  fn check(& self, _: & VarMap<VarInfo>) -> Res<()> {
    Ok(())
  }

  /// Propagates equalities in a clause.
  ///
  /// Returns `true` if the clause should_be_removed.
  ///
  /// Assumes equalities have arity `2`.
  pub fn clause_propagate(& mut self, clause: & mut Clause) -> Res<bool> {
    self.var_to_rep.clear() ;
    self.var_to_rep_term.clear() ;
    self.rep_to_vars.clear() ;
    self.rep_to_term.clear() ;
    self.rep_to_stable_term.clear() ;
    self.terms_to_add.clear() ;
    self.eqs.clear() ;
    let mut remove ;

    // Find equalities in `lhs`.
    for term in & clause.lhs_terms {
      if let Some((Op::Eql, _)) = term.app_inspect() {
        self.eqs.push( term.clone() )
      }
    }

    while let Some(eq) = self.eqs.pop() {
      remove = true ;
      log_debug!{ "  looking at equality {}", eq }

      let args = if let Some(args) = eq.kids() { args } else {
        unreachable!(
          "clause_propagate: not equality after checking that it is"
        )
      } ;
      if args.len() != 2 {
        bail!(
          "simplification for equality over more \
          than 2 terms is unimplemented"
        )
      }

      match (args[0].var_idx(), args[1].var_idx()) {

        (Some(v_1), Some(v_2)) if v_1 == v_2 => (),

        (Some(v_1), Some(v_2)) => match (
          self.var_to_rep.get(& v_1).map(|rep| * rep),
          self.var_to_rep.get(& v_2).map(|rep| * rep)
        ) {

          // Both already have same rep.
          (Some(rep_1), Some(rep_2)) if rep_1 == rep_2 => (),
          // Different rep.
          (Some(rep_1), Some(rep_2)) => {
            // We keep `rep_1`.
            let set_2 = if let Some(set) = self.rep_to_vars.remove(& rep_2) {
              set
            } else { bail!("simplification error (1)") } ;
            let mut set_1 = if let Some(set) = self.rep_to_vars.get_mut(& rep_1) {
              set
            } else { bail!("simplification error (2)") } ;
            // Drain `set_2`: update `var_to_rep` and `set_1`.
            use mylib::coll::* ;
            for var in set_2.into_iter().chain_one(rep_2) {
              let _prev = self.var_to_rep.insert(var, rep_1) ;
              debug_assert_eq!( _prev, Some(rep_2) ) ;
              let _is_new = set_1.insert(var) ;
              debug_assert!( _is_new )
            }
            // Re-route `rep_to_term`.
            if let Some(term) = self.rep_to_term.remove(& rep_2) {
              let prev = self.rep_to_term.insert(rep_1, term.clone()) ;
              if let Some(other_term) = prev {
                self.terms_to_add.push( term::eq(term, other_term) )
              }
            }
          },
          // Only `v_1` has a rep.
          (Some(rep_1), None) => {
            let mut set_1 = if let Some(set) = self.rep_to_vars.get_mut(& rep_1) {
              set
            } else { panic!("simplification error (3)") } ;
            let _is_new = set_1.insert(v_2) ;
            debug_assert!( _is_new ) ;
            let _prev = self.var_to_rep.insert(v_2, rep_1) ;
            debug_assert!( _prev.is_none() )
          },
          // Only `v_2` has a rep.
          (None, Some(rep_2)) => {
            let mut set_2 = if let Some(set) = self.rep_to_vars.get_mut(& rep_2) {
              set
            } else { bail!("simplification error (4)") } ;
            let _is_new = set_2.insert(v_1) ;
            debug_assert!( _is_new ) ;
            let _prev = self.var_to_rep.insert(v_1, rep_2) ;
            debug_assert!( _prev.is_none() )
          },
          // No rep, we use `v_1` as the rep.
          (None, None) => {
            let mut set = VarSet::with_capacity(4) ;
            set.insert(v_2) ;
            let _prev = self.rep_to_vars.insert(v_1, set) ;
            debug_assert!( _prev.is_none() ) ;
            let _prev = self.var_to_rep.insert(v_1, v_1) ;
            debug_assert!( _prev.is_none() ) ;
            let _prev = self.var_to_rep.insert(v_2, v_1) ;
            debug_assert!( _prev.is_none() ) ;
          },

        },

        // A variable and a term.
        (Some(var), None) | (None, Some(var)) => {
          let term = if args[0].var_idx().is_some() {
            args[1].clone()
          } else { args[0].clone() } ;
          let rep = if let Some(rep) = self.var_to_rep.get(& var).map(
            |rep| * rep
          ) { rep } else {
            let _prev = self.var_to_rep.insert(var, var) ;
            debug_assert!( _prev.is_none() ) ;
            let _prev = self.rep_to_vars.insert(
              var, VarSet::with_capacity(4)
            ) ;
            debug_assert!( _prev.is_none() ) ;
            var
          } ;
          log_debug!{ "rep of {} is {}", var, rep }
          let prev = self.rep_to_term.insert(rep, term.clone()) ;
          if let Some(prev) = prev {
            let eq = term::eq(prev, term) ;
            match eq.eval( & VarMap::with_capacity(0) ) {
              Ok(Val::B(true)) => (),
              Ok(Val::B(false)) => return Ok(true),
              Ok(Val::I(_)) => bail!("equality evaluation yielded integer"),
              _ => self.terms_to_add.push(eq),
            }
          }
        },

        // Two terms.
        (None, None) => {
          let inline = if clause.lhs_terms.contains(& args[0]) {
            Some( args[1].clone() )
          } else if clause.lhs_terms.contains(& args[1]) {
            Some( args[0].clone() )
          } else {
            let not_lhs = term::not( args[0].clone() ) ;
            let not_rhs = term::not( args[1].clone() ) ;
            if clause.lhs_terms.contains(& not_lhs) {
              Some(not_rhs)
            } else if clause.lhs_terms.contains(& not_rhs) {
              Some(not_lhs)
            } else {
              None
            }
          } ;
          if let Some(term) = inline {
            clause.insert_term( term.clone() ) ;
            remove = true ;
            if term.is_eq() {
              self.eqs.push(term)
            } else {
              self.terms_to_add.push(term)
            }
          } else {
            remove = false
          }
        },

      }

      if remove {
        log_debug!{ "  removing..." }
        let was_there = clause.lhs_terms.remove(& eq) ;
        debug_assert!(was_there)
      } else {
        log_debug!{ "  skipping..." }
      }
    }

    self.check( clause.vars() ) ? ;

    log_debug!{ "  generating `var_to_rep_term`" }
    self.var_to_rep_term = VarHMap::with_capacity( self.var_to_rep.len() ) ;
    for (rep, set) in & self.rep_to_vars {
      for var in set {
        if var != rep {
          let _prev = self.var_to_rep_term.insert(* var, term::var(* rep)) ;
          debug_assert!( _prev.is_none() )
        }
      }
    }
    if_debug!{
      for (var, rep) in & self.var_to_rep {
        log_debug!{ "    {} -> {}", var, rep }
      }
    }

    log_debug!{ "  stabilizing `rep_to_term` (first step)" }
    for (_, term) in & mut self.rep_to_term {
      let (nu_term, changed) = term.subst(& self.var_to_rep_term) ;
      if changed { * term = nu_term }
    }
    let mut to_rm = vec![] ;
    for (rep, term) in & self.rep_to_term {
      log_debug!{ "    {} -> {}", rep, term }
      if term.vars().contains(rep) {
        log_debug!{ "      -> recursive, putting equality back." }
        to_rm.push(* rep)
      }
    }
    for to_rm in to_rm {
      let term = self.rep_to_term.remove(& to_rm).ok_or::<Error>(
        "unreachable".into()
      ) ? ;
      self.terms_to_add.push(
        term::eq( term::var(to_rm), term )
      )
    }

    log_debug!{
      "  stabilizing `rep_to_term` (second step, {})",
      self.rep_to_term.len()
    }
    // self.rep_to_stable_term = VarHMap::with_capacity(self.rep_to_term.len()) ;
    for (rep, term) in & self.rep_to_term {
      let (nu_term, _) = term.subst_fp(& self.rep_to_term) ;
      let _prev = self.rep_to_stable_term.insert(* rep, nu_term) ;
      debug_assert!( _prev.is_none() )
    }
    if_debug!{
      for (rep, term) in & self.rep_to_stable_term {
        log_debug!{ "    {} -> {}", rep, term }
      }
    }

    // Note that clause variable de-activation is done in this loop.
    log_debug!{ "  completing substitution" }
    for (rep, vars) in self.rep_to_vars.drain() {
      log_debug!{"  - rep {}", rep}
      let term = if let Some(term) = self.rep_to_stable_term.get(& rep) {
        clause.vars[rep].active = false ;
        term.clone()
      } else {
        debug_assert!( clause.vars[rep].active ) ;
        term::var(rep)
      } ;
      for var in vars {
        if var != rep {
          log_debug!{"    var: {}", var}
          clause.vars[var].active = false ;
          let _prev = self.rep_to_stable_term.insert(var, term.clone()) ;
          debug_assert_eq!( _prev, None )
        }
      }
    }
    if_debug!{
      for (rep, term) in & self.rep_to_stable_term {
        log_debug!{ "    {} -> {}", rep, term }
      }
    }

    for term in self.terms_to_add.drain(0..) {
      clause.insert_term(term) ;
    }

    log_debug!{ "  updating clause's terms" }
    clause.subst(& self.rep_to_stable_term) ;

    Ok(false)
  }
}