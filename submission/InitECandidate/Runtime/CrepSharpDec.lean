import InitECandidate.Runtime.CrepSharpLeaf
import InitECandidate.Runtime.SourceCostSharpCrepDec
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

namespace SharpModel
variable (M : SharpModel) {fn : CName}

/-- Executed work of nested declarations whose initializers all succeed and do
not read the declared names: one entry and initializer per slot, then the body
in the state with all slots bound. -/
theorem work_nestedDecs_eval {σ : Type} (expressions : List (CrepExpHOL 64))
    (names : List Nat) (values : List (HolWordLab 64)) (body : CrepProgHOL 64)
    (t : CrepSemHOLState 64 σ) (bodyWork : Nat)
    (evaluated : expressions.map (evalCrepSemHOLExp t) = values.map some)
    (lengths : names.length = expressions.length)
    (distinct : distinctListsHol names (expressions.flatMap crepExpVarsHOL) = true)
    (nodup : names.Nodup)
    (bodyRun : CrepWorkM M fn { t with locals := t.locals.updateListEq (names.zip values) } body
      bodyWork) :
    CrepWorkM M fn t (nestedDecsHOL names expressions body)
      (M.prs expressions + bodyWork) := by
  induction expressions generalizing names values t with
  | nil =>
    cases names with
    | cons => simp at lengths
    | nil =>
      cases values with
      | cons => simp at evaluated
      | nil =>
        simp only [nestedDecsHOL, List.length_nil, prs_nil, Nat.zero_add]
        have : ({ t with locals := t.locals.updateListEq ([] : List (Nat × HolWordLab 64)) } :
            CrepSemHOLState 64 σ) = t := by
          cases t; simp only [CrepSemHOLState.mk.injEq, and_true]
          apply HolFiniteMapExact.ext; funext k; rfl
        simpa [List.zip_nil_left, this] using bodyRun
  | cons expression expressions ih =>
    cases names with
    | nil => simp at lengths
    | cons name names =>
      cases values with
      | nil => simp at evaluated
      | cons value values =>
        simp only [List.map_cons, List.cons.injEq] at evaluated
        obtain ⟨head, tail⟩ := evaluated
        have disjoint := (distinctListsHol_eq_true_iff_listDisjoint _ _).mp distinct
        have notTail : ∀ e, e ∈ expressions → name ∉ crepExpVarsHOL e := by
          intro e he hmem
          exact disjoint name (by simp) (List.mem_flatMap.mpr ⟨e, by simp [he], hmem⟩)
        let bound : CrepSemHOLState 64 σ := { t with locals := t.locals.updateEq (name, value) }
        have tailBound : expressions.map (evalCrepSemHOLExp bound) = values.map some := by
          rw [← tail]
          apply List.map_congr_left
          intro e he
          exact evalCrepSemHOLExp_updateLocals_eq_of_not_vars t e name value (notTail e he)
        have distinctTail :
            distinctListsHol names (expressions.flatMap crepExpVarsHOL) = true := by
          apply (distinctListsHol_eq_true_iff_listDisjoint _ _).mpr
          intro n hn hvars
          exact disjoint n (by simp [hn])
            (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr hvars)
        have bodyState : ({ bound with locals := bound.locals.updateListEq (names.zip values) } :
            CrepSemHOLState 64 σ) =
            { t with locals := t.locals.updateListEq ((name :: names).zip (value :: values)) } := by
          simp only [bound, List.zip_cons_cons, updateListEq_cons_eq]
        have rest := ih names values bound tailBound (by simpa using lengths) distinctTail
          (List.nodup_cons.mp nodup).2 (by rw [bodyState]; exact bodyRun)
        simp only [nestedDecsHOL, List.length_cons, prs_cons]
        have := CrepWorkF.dec (name := name) (body := nestedDecsHOL names expressions body) head rest
        refine (congrArg (CrepWorkM M fn t _) ?_).mp this
        omega

/-- Source declaration lowering: after the compiled initializer fills fresh
slots, the compiled body runs in a state satisfying all original simulation
premises for the extended context. -/
theorem dec_transfer {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {name : MlStringHOL} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64} {value : ValueHOL 64}
    (evaluated : expressionValue s initializer = some value)
    (shapeMatch : shapeEqHOL shape (shapeOfHOLExact value) = true)
    (rel : SourceCrepRel context s t) (localised : localisedExpHOL initializer = true) :
    ∃ bodyContext bodyState, bodyContext = decCallCtxt context name (shapeOfHOLExact value) ∧
      bodyContext.funcs = context.funcs ∧
      SourceCrepRel bodyContext (setVarHOLFinite name value s) bodyState ∧
      ∀ bodyWork, CrepWorkM M fn bodyState (compileProgExactHOLW bodyContext body) bodyWork →
        CrepWorkM M fn t (compileProgExactHOLW context (.dec name shape initializer body))
          (M.prs (compileExpExactHOLW context initializer).1 +
            bodyWork) := by
  classical
  rcases hc : compileExpExactHOLW context initializer with ⟨es, cs⟩
  obtain ⟨hes, hlen, hcs, hwf⟩ :=
    @compileExpValRelHOL 64 F _ s
      (fun address => Classical.propDecidable (s.memaddrs address)) context t
      (fun address => Classical.propDecidable (t.memaddrs address))
      initializer value es cs evaluated rel.state rel.code rel.locals localised hc
  subst hcs
  have hnodup := decCallSlots_nodup context (shapeOfHOLExact value)
  have hflen : (flattenHOL value).length = sizeOfShapeHOL (shapeOfHOLExact value) :=
    flattenHOL_length_eq_sizeOfShapeHOL value hwf
  have hslen : (decCallSlots context (shapeOfHOLExact value)).length = es.length := by
    simp [decCallSlots, hlen]
  have hdist : distinctListsHol (decCallSlots context (shapeOfHOLExact value))
      (es.flatMap crepExpVarsHOL) = true := by
    simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq]
    intro x hx hmem
    have hmem' : x ∈ (compileExpExactHOLW context initializer).1.flatMap crepExpVarsHOL := by
      rw [hc]; exact hmem
    obtain ⟨src, sh', slots, hlk, hslot⟩ :=
      (compileExpExactHOLW_vars_from_context context).1 initializer x hmem'
    have := rel.locals.2.1.2 src sh' slots hlk x hslot
    have := (decCallSlots_gt context _ x hx).1
    omega
  have hcomp : compileProgExactHOLW context (.dec name shape initializer body) =
      nestedDecsHOL (decCallSlots context (shapeOfHOLExact value)) es
        (compileProgExactHOLW (decCallCtxt context name (shapeOfHOLExact value)) body) := by
    simp only [compileProgExactHOLW, compileDecExactHOLW, hc]
    rw [if_neg (by rw [← hlen]; simp)]
  have hlocc := localsRelExtendNewVarHOL context s.locals t.locals value name
    (decCallSlots context (shapeOfHOLExact value))
    ⟨rel.locals, hwf, hnodup, fun y hy => decCallSlots_gt context _ y hy,
      by simp [decCallSlots]⟩
  let slotEntries := (decCallSlots context (shapeOfHOLExact value)).zip (flattenHOL value)
  refine ⟨decCallCtxt context name (shapeOfHOLExact value),
    ({ t with locals := t.locals.updateListEq slotEntries } : CrepSemHOLState 64 F), rfl, rfl,
    ⟨by simpa [panToCrepStateRelFiniteExact, setVarHOLFinite] using rel.state, rel.code,
      rel.exceptions, hlocc⟩,
    ?_⟩
  intro bodyWork bodyRun
  rw [hcomp]
  have work := M.work_nestedDecs_eval es (decCallSlots context (shapeOfHOLExact value))
    (flattenHOL value) _ t bodyWork hes hslen hdist hnodup bodyRun
  exact work

end SharpModel

#print axioms SharpModel.work_nestedDecs_eval
#print axioms SharpModel.dec_transfer
end InitECandidate.Runtime.FineCost
