import InitECandidate.Runtime.WordColourPrice
import InitECandidate.Runtime.WordCseAtomicCost
import InitECandidate.Runtime.WordCompileExpCost
import InitECandidate.Runtime.WordPermuteGlobalCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-!
# Quantitative register colouring: motive and structural cases

`ColourCostPost` is HOL `evaluate_apply_colour`'s conclusion with one extra
conjunct: under the SAME existential source permutation, the coloured run's
executed work is at most the source run's work. Both runs are priced by one
pure price that colouring does not increase. No target run, budget or clock is
assumed; every case below rebuilds the actual coloured execution.
-/

/-- A price that never increases under colouring. -/
def ColourPriceInvariant (price : WordLangProgHOL (BitVec 64) → Nat) : Prop :=
  ∀ (f : Nat → Nat) (p : WordLangProgHOL (BitVec 64)), price (applyColour f p) ≤ price p

/-- Quantitative `evaluate_apply_colour` conclusion: one source permutation
carries the result, frame, live-scoped locals and the cost comparison. -/
def ColourCostPost {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat) (f : Nat → Nat)
    (prog : WordLangProgHOL (BitVec 64)) (live : NumSet) (lt : List (NumSet × NumSet))
    (st cst : WordSemStateFiniteExact 64 C F) : Prop :=
  ∃ permutation : Nat → Nat → Nat,
    let sourceState := {st with permute := permutation}
    let sourceRun := evaluate prog sourceState
    let targetRun := evaluate (applyColour f prog) cst
    sourceRun.1 = some .error ∨
      sourceRun.1 = targetRun.1 ∧ wordStateEqRel sourceRun.2 targetRun.2 ∧
        applyColourLocals f live lt sourceRun.1 sourceRun.2.locals targetRun.2.locals ∧
        wordExecutionCost (fun p _ => price p) (applyColour f prog) cst ≤
          wordExecutionCost (fun p _ => price p) prog sourceState

/-- `evaluate_apply_colour`'s premises with the quantitative conclusion. -/
def ColourCostGoal (C F : Type) (price : WordLangProgHOL (BitVec 64) → Nat)
    (prog : WordLangProgHOL (BitVec 64)) : Prop :=
  ∀ (st cst : WordSemStateFiniteExact 64 C F) (f : Nat → Nat) (live : NumSet)
    (lt : List (NumSet × NumSet)),
    colouringOk f prog live lt ∧ wordStateEqRel st cst ∧
      strongLocalsRel f (sptDomain (getLive prog live lt)) st.locals cst.locals →
    ColourCostPost price f prog live lt st cst

/-- Forgetting work recovers HOL `evaluate_apply_colour` with the same witness. -/
theorem ColourCostPost.semantic {C F : Type} {price : WordLangProgHOL (BitVec 64) → Nat}
    {f : Nat → Nat} {prog : WordLangProgHOL (BitVec 64)} {live : NumSet}
    {lt : List (NumSet × NumSet)} {st cst : WordSemStateFiniteExact 64 C F}
    (post : ColourCostPost price f prog live lt st cst) : applyColourPost f prog live lt st cst := by
  classical
  obtain ⟨permutation, related⟩ := post
  refine ⟨permutation, ?_⟩
  dsimp only at related
  rcases sourceEval : evaluate prog {st with permute := permutation} with ⟨result, after⟩
  rw [sourceEval] at related
  dsimp only at related ⊢
  by_cases error : result = some .error
  · rw [if_pos error]; trivial
  · rw [if_neg error]
    rcases related with bad | ⟨same, frame, locals, _⟩
    · exact (error bad).elim
    · rcases targetEval : evaluate (applyColour f prog) cst with ⟨targetResult, targetAfter⟩
      rw [targetEval] at same frame locals
      exact ⟨same, frame, locals⟩

/-- Unpack the semantic conclusion at its own witness. -/
theorem applyColourPost_unpack {C F : Type} {f : Nat → Nat}
    {prog : WordLangProgHOL (BitVec 64)} {live : NumSet} {lt : List (NumSet × NumSet)}
    {st cst : WordSemStateFiniteExact 64 C F} (post : applyColourPost f prog live lt st cst) :
    ∃ permutation : Nat → Nat → Nat,
      let sourceRun := evaluate prog {st with permute := permutation}
      let targetRun := evaluate (applyColour f prog) cst
      sourceRun.1 = some .error ∨
        sourceRun.1 = targetRun.1 ∧ wordStateEqRel sourceRun.2 targetRun.2 ∧
          applyColourLocals f live lt sourceRun.1 sourceRun.2.locals targetRun.2.locals := by
  classical
  obtain ⟨permutation, related⟩ := post
  refine ⟨permutation, ?_⟩
  rcases sourceEval : evaluate prog {st with permute := permutation} with ⟨result, after⟩
  rw [sourceEval] at related
  dsimp only at related ⊢
  by_cases error : result = some .error
  · exact Or.inl error
  · rw [if_neg error] at related
    rcases targetEval : evaluate (applyColour f prog) cst with ⟨targetResult, targetAfter⟩
    rw [targetEval] at related
    exact Or.inr related

theorem wordCostAtomic_applyColour (f : Nat → Nat) (prog : WordLangProgHOL (BitVec 64))
    (atomic : wordCostAtomic prog = true) : wordCostAtomic (applyColour f prog) = true := by
  cases prog <;> simp_all [applyColour, wordCostAtomic]

/-- Every atomic constructor: its work is its own price on both sides. -/
theorem colourCost_atomic {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (prog : WordLangProgHOL (BitVec 64))
    (atomic : wordCostAtomic prog = true) (semantic : applyColourGoal C F prog) :
    ColourCostGoal C F price prog := by
  intro st cst f live lt premises
  obtain ⟨permutation, related⟩ := applyColourPost_unpack (semantic st cst f live lt premises)
  refine ⟨permutation, ?_⟩
  dsimp only at related ⊢
  rcases related with bad | ⟨same, frame, locals⟩
  · exact Or.inl bad
  · refine Or.inr ⟨same, frame, locals, ?_⟩
    rw [wordExecutionCost_atomic _ _ _ (wordCostAtomic_applyColour f prog atomic),
      wordExecutionCost_atomic _ _ _ atomic]
    exact invariant f prog

/-- Sequence: the prefix witness is restitched through the actual suffix
witness; the prefix cost is preserved exactly by that restitching. -/
theorem colourCost_seq {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (first second : WordLangProgHOL (BitVec 64))
    (ihFirst : ColourCostGoal C F price first) (ihSecond : ColourCostGoal C F price second) :
    ColourCostGoal C F price (.seq first second) := by
  rintro st cst f live lt ⟨hc, hs, hl⟩
  obtain ⟨p1, hp1⟩ := ihFirst st cst f (getLive second live lt) lt
    ⟨hc.2.2, hs, by simpa only [getLive] using hl⟩
  dsimp only at hp1
  rcases he1 : evaluate first {st with permute := p1} with ⟨r1, s1⟩
  rw [he1] at hp1
  dsimp only at hp1
  rcases hp1 with bad | ⟨same1, frame1, locals1, cost1⟩
  · refine ⟨p1, Or.inl ?_⟩
    rw [evaluate, fix_clock_evaluate, he1]
    subst bad
    rfl
  rcases hec1 : evaluate (applyColour f first) cst with ⟨rc1, cs1⟩
  rw [hec1] at same1 frame1 locals1
  dsimp only at same1 frame1 locals1
  subst rc1
  have targetSeq : applyColour f (.seq first second) =
      .seq (applyColour f first) (applyColour f second) := rfl
  cases r1 with
  | some result =>
    refine ⟨p1, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [targetSeq, evaluate, fix_clock_evaluate, he1, evaluate, fix_clock_evaluate, hec1]
    · rw [targetSeq, evaluate, fix_clock_evaluate, he1, evaluate, fix_clock_evaluate, hec1]
      exact frame1
    · rw [targetSeq, evaluate, fix_clock_evaluate, he1, evaluate, fix_clock_evaluate, hec1]
      cases result <;> exact locals1
    · rw [targetSeq, wordExecutionCost_seq, wordExecutionCost_seq, hec1, he1]
      simp only [Nat.add_zero]
      have head := invariant f (.seq first second)
      rw [targetSeq] at head
      exact Nat.add_le_add head cost1
  | none =>
    obtain ⟨p2, hp2⟩ := ihSecond s1 cs1 f live lt ⟨hc.2.1, frame1, locals1⟩
    dsimp only at hp2
    obtain ⟨p0, run0, cost0⟩ := word_permute_executed_cost price first
      {st with permute := p1} p2 (by rw [he1]; simp)
    rw [he1] at run0
    have run0' : evaluate first {st with permute := p0} = (none, {s1 with permute := p2}) := run0
    have cost0' : wordExecutionCost (fun p _ => price p) first {st with permute := p0} =
        wordExecutionCost (fun p _ => price p) first {st with permute := p1} := cost0
    refine ⟨p0, ?_⟩
    dsimp only
    rw [targetSeq, evaluate, fix_clock_evaluate, run0', evaluate, fix_clock_evaluate, hec1]
    dsimp only
    rcases hp2 with bad | ⟨same2, frame2, locals2, cost2⟩
    · exact Or.inl bad
    · refine Or.inr ⟨same2, frame2, locals2, ?_⟩
      rw [wordExecutionCost_seq, wordExecutionCost_seq, hec1, run0']
      simp only
      rw [cost0']
      have head := invariant f (.seq first second)
      rw [targetSeq] at head
      omega

/-- Conditional: both sides select the same arm from related registers. -/
theorem colourCost_ite {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (cmp : Cmp) (left : Nat)
    (right : WordRegImm (BitVec 64)) (yes no : WordLangProgHOL (BitVec 64))
    (ihYes : ColourCostGoal C F price yes) (ihNo : ColourCostGoal C F price no) :
    ColourCostGoal C F price (.ite cmp left right yes no) := by
  rintro st cst f live lt ⟨hc, hs, hl⟩
  have hv : ∀ perm : Nat → Nat → Nat,
      getVar left {st with permute := perm} = getVar left st := fun _ => rfl
  have hi : ∀ perm : Nat → Nat → Nat,
      getVarImm right {st with permute := perm} = getVarImm right st := by
    intro perm; cases right <;> rfl
  have hm : ∀ key, sptDomain (sptUnion (getLive yes live lt) (getLive no live lt)) key →
      sptDomain (getLive (.ite cmp left right yes no) live lt) key := by
    intro key hk
    cases right <;> simp only [getLive]
    case imm => exact (sptDomain_ins _ _ _ key).mpr (Or.inr hk)
    case reg => exact (sptDomain_ins _ _ _ key).mpr (Or.inr
        ((sptDomain_ins _ _ _ key).mpr (Or.inr hk)))
  have hleft : sptDomain (getLive (.ite cmp left right yes no) live lt) left := by
    cases right <;> simp only [getLive]
    case imm => exact (sptDomain_ins _ _ _ left).mpr (Or.inl rfl)
    case reg => exact (sptDomain_ins _ _ _ left).mpr (Or.inr
        ((sptDomain_ins _ _ _ left).mpr (Or.inl rfl)))
  have targetIte : applyColour f (.ite cmp left right yes no) =
      .ite cmp (f left) (applyColourImm f right) (applyColour f yes) (applyColour f no) := rfl
  have stuck : ∀ (stop : (evaluate (.ite cmp left right yes no) st).1 = some .error),
      ColourCostPost price f (.ite cmp left right yes no) live lt st cst := by
    intro stop
    refine ⟨st.permute, Or.inl ?_⟩
    exact stop
  cases hx : getVar left st with
  | none => exact stuck (by rw [evaluate, hx])
  | some x =>
    cases hy : getVarImm right st with
    | none => exact stuck (by rw [evaluate, hx, hy])
    | some y =>
      have hcx := strongLocalsRelGetVar f _ st cst left x ⟨hl, hleft, hx⟩
      have hcy := strongLocalsRelGetVarImm f _ st cst right y ⟨hl, by
        cases right <;> simp only [getLive]
        case reg => exact (sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hy⟩
      cases hw : wordSemWordCmp cmp x y with
      | none => exact stuck (by rw [evaluate, hx, hy]; simp [hw])
      | some decision =>
        have branch : ∀ (arm : WordLangProgHOL (BitVec 64))
            (armIH : ColourCostGoal C F price arm)
            (armLive : ∀ key, sptDomain (getLive arm live lt) key →
              sptDomain (sptUnion (getLive yes live lt) (getLive no live lt)) key)
            (armOk : colouringOk f arm live lt)
            (sourceSel : ∀ s : WordSemStateFiniteExact 64 C F, getVar left s = some x →
              getVarImm right s = some y →
              evaluate (.ite cmp left right yes no) s = evaluate arm s)
            (targetSel : evaluate (applyColour f (.ite cmp left right yes no)) cst =
              evaluate (applyColour f arm) cst)
            (sourceCost : ∀ s : WordSemStateFiniteExact 64 C F, getVar left s = some x →
              getVarImm right s = some y →
              wordExecutionCost (fun p _ => price p) (.ite cmp left right yes no) s =
                price (.ite cmp left right yes no) + wordExecutionCost (fun p _ => price p) arm s)
            (targetCost : wordExecutionCost (fun p _ => price p)
              (applyColour f (.ite cmp left right yes no)) cst =
                price (applyColour f (.ite cmp left right yes no)) +
                  wordExecutionCost (fun p _ => price p) (applyColour f arm) cst),
            ColourCostPost price f (.ite cmp left right yes no) live lt st cst := by
          intro arm armIH armLive armOk sourceSel targetSel sourceCost targetCost
          obtain ⟨perm, hp⟩ := armIH st cst f live lt
            ⟨armOk, hs, slrMono hl (fun k hk => hm k (armLive k hk))⟩
          refine ⟨perm, ?_⟩
          dsimp only at hp ⊢
          rw [sourceSel _ (by rw [hv]; exact hx) (by rw [hi]; exact hy), targetSel,
            sourceCost _ (by rw [hv]; exact hx) (by rw [hi]; exact hy), targetCost]
          rcases hp with bad | ⟨same, frame, locals, cost⟩
          · exact Or.inl bad
          · exact Or.inr ⟨same, frame, locals,
              Nat.add_le_add (invariant f _) cost⟩
        cases decision with
        | true =>
          apply branch yes ihYes (fun k hk => (sptDomain_uni _ _ k).mpr (Or.inl hk)) hc.2.1
          · intro s gx gy; rw [evaluate, gx, gy]; simp only [hw]
          · rw [targetIte, evaluate, hcx, hcy]; simp only [hw]
          · intro s gx gy; rw [wordExecutionCost_ite, gx, gy]; simp only [hw]
          · rw [targetIte, wordExecutionCost_ite, hcx, hcy]; simp only [hw]
        | false =>
          apply branch no ihNo (fun k hk => (sptDomain_uni _ _ k).mpr (Or.inr hk)) hc.2.2
          · intro s gx gy; rw [evaluate, gx, gy]; simp only [hw]
          · rw [targetIte, evaluate, hcx, hcy]; simp only [hw]
          · intro s gx gy; rw [wordExecutionCost_ite, gx, gy]; simp only [hw]
          · rw [targetIte, wordExecutionCost_ite, hcx, hcy]; simp only [hw]

theorem wordExecutionCost_mustTerminate {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (body : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost price (.mustTerminate body) s = price (.mustTerminate body) s +
      if s.termdep = 0 then 0
      else wordExecutionCost price body
        {s with clock := wordSemMustTerminateLimit 64, termdep := s.termdep - 1} := by
  rw [wordExecutionCost]
  by_cases zero : s.termdep = 0 <;> simp [zero]

/-- The single result that MustTerminate turns into an error. -/
def resultIsTimeOut : Option (WordSemResult 64) → Bool
  | some .timeOut => true
  | _ => false

/-- MustTerminate: the body runs from the same reset clock on both sides. -/
theorem colourCost_mustTerminate {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (body : WordLangProgHOL (BitVec 64))
    (ih : ColourCostGoal C F price body) :
    ColourCostGoal C F price (.mustTerminate body) := by
  rintro st cst f live lt ⟨hc, hs, hl⟩
  have hdep : cst.termdep = st.termdep := by simp_all [wordStateEqRel]
  by_cases hz : st.termdep = 0
  · refine ⟨st.permute, Or.inl ?_⟩
    rw [evaluate]
    simp [hz]
  · have hclk := wsrClock hs
    let s := {st with clock := wordSemMustTerminateLimit 64, termdep := st.termdep - 1}
    let cs := {cst with clock := wordSemMustTerminateLimit 64, termdep := cst.termdep - 1}
    have hsc : wordStateEqRel s cs := by simp_all [s, cs, wordStateEqRel]
    obtain ⟨perm, hp⟩ := ih s cs f live lt ⟨hc, hsc, by simpa only [getLive] using hl⟩
    rcases he : evaluate body {s with permute := perm} with ⟨res, rs⟩
    dsimp only at hp
    rw [he] at hp
    dsimp only at hp
    refine ⟨perm, ?_⟩
    have hein : evaluate body
        { { st with permute := perm } with clock := wordSemMustTerminateLimit 64, termdep := st.termdep - 1 } =
          (res, rs) := he
    have sourceCost : wordExecutionCost (fun p _ => price p) (.mustTerminate body)
        {st with permute := perm} = price (.mustTerminate body) +
          wordExecutionCost (fun p _ => price p) body {s with permute := perm} := by
      rw [wordExecutionCost_mustTerminate]
      simp only [hz, if_false]
      rfl
    have targetCost : wordExecutionCost (fun p _ => price p) (applyColour f (.mustTerminate body))
        cst = price (applyColour f (.mustTerminate body)) +
          wordExecutionCost (fun p _ => price p) (applyColour f body) cs := by
      show wordExecutionCost _ (.mustTerminate (applyColour f body)) cst = _
      have czero : ¬ cst.termdep = 0 := by rw [hdep]; exact hz
      rw [wordExecutionCost_mustTerminate, if_neg czero]
      rfl
    dsimp only
    rw [sourceCost, targetCost]
    rcases hp with bad | ⟨same, frame, locals, cost⟩
    · left
      subst res
      rw [evaluate]
      simp only [dif_neg hz]
      rw [hein]
    have costBound := Nat.add_le_add (invariant f (.mustTerminate body)) cost
    rcases hec : evaluate (applyColour f body) cs with ⟨resc, rcs⟩
    rw [hec] at same frame locals
    dsimp only at same frame locals
    subst resc
    have hcein : evaluate (applyColour f body)
        {cst with clock := wordSemMustTerminateLimit 64, termdep := st.termdep - 1} =
          (res, rcs) := by simpa only [cs, hdep] using hec
    have sourceRun : evaluate (.mustTerminate body) {st with permute := perm} =
        (if resultIsTimeOut res then (some .error, {st with permute := perm})
         else (res, {rs with clock := st.clock, termdep := st.termdep})) := by
      rw [evaluate]
      simp only [dif_neg hz]
      rw [hein]
      split <;> simp_all [resultIsTimeOut]
    have targetRun : evaluate (applyColour f (.mustTerminate body)) cst =
        (if resultIsTimeOut res then (some .error, cst)
         else (res, {rcs with clock := cst.clock, termdep := cst.termdep})) := by
      show evaluate (.mustTerminate (applyColour f body)) cst = _
      rw [evaluate]
      simp only [hdep, dif_neg hz]
      rw [hcein]
      split <;> simp_all [resultIsTimeOut]
    rw [sourceRun, targetRun]
    cases res with
    | none =>
      simp only [resultIsTimeOut, Bool.false_eq_true, if_false]
      refine Or.inr ⟨by trivial, ?_, ?_, costBound⟩
      · simp_all [wordStateEqRel]
      · simpa [applyColourLocals] using locals
    | some result =>
      cases result with
      | timeOut => simp only [resultIsTimeOut, if_true]; exact Or.inl (by trivial)
      | error => simp only [resultIsTimeOut, Bool.false_eq_true, if_false]; exact Or.inl (by trivial)
      | _ =>
        simp only [resultIsTimeOut, Bool.false_eq_true, if_false]
        refine Or.inr ⟨by trivial, ?_, ?_, costBound⟩
        · simp_all [wordStateEqRel]
        · simpa [applyColourLocals] using locals

#print axioms ColourCostPost.semantic
#print axioms colourCost_atomic
#print axioms colourCost_seq
#print axioms colourCost_ite
#print axioms colourCost_mustTerminate
end InitECandidate.Runtime.FineCost
