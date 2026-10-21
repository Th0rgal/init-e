import InitECandidate.Runtime.WordColourIndexedBasis
import InitECandidate.Runtime.WordIselLoop

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

section Unfold
variable {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
  (function : Nat)

theorem wordFunctionExecutionCost_ite (cmp : Cmp) (lhs : Nat) (rhs : WordRegImm (BitVec 64))
    (a b : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordFunctionExecutionCost price function (.ite cmp lhs rhs a b) s =
      price function (.ite cmp lhs rhs a b) s +
      match getVar lhs s, getVarImm rhs s with
      | some x, some y => match wordSemWordCmp cmp x y with
        | some true => wordFunctionExecutionCost price function a s
        | some false => wordFunctionExecutionCost price function b s
        | none => 0
      | _, _ => 0 := by
  rw [wordFunctionExecutionCost]
  rcases getVar lhs s with _ | x <;> rcases getVarImm rhs s with _ | y <;> simp only
  rcases wordSemWordCmp cmp x y with _ | _ | _ <;> rfl

theorem wordFunctionExecutionCost_mustTerminate (body : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) :
    wordFunctionExecutionCost price function (.mustTerminate body) s =
      price function (.mustTerminate body) s +
      if s.termdep = 0 then 0
      else wordFunctionExecutionCost price function body
        {s with clock := wordSemMustTerminateLimit 64, termdep := s.termdep - 1} := by
  rw [wordFunctionExecutionCost]
  by_cases zero : s.termdep = 0 <;> simp [zero]

theorem function_loop_cost_clause (names : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (exitNames : WordLangNumSetHOL) (s cs : WordSemStateFiniteExact 64 C F)
    (hcs : cutState (names, .ln) s = some cs)
    (r1 : Option (WordSemResult 64)) (s1 : WordSemStateFiniteExact 64 C F) (hb : evaluate body cs = (r1, s1)) :
    wordFunctionExecutionCost price function (.loop names body exitNames) s =
      price function (.loop names body exitNames) s + wordFunctionExecutionCost price function body cs +
        (if wordSemContLoop r1 then
          (if s1.clock = 0 then 0
           else wordFunctionExecutionCost price function (.loop names body exitNames) (decClock s1))
         else 0) := by
  rw [wordFunctionExecutionCost]
  split
  · rename_i h; rw [hcs] at h; cases h
  · rename_i cs' h
    rw [hcs] at h; cases h
    have hf : fixClock cs (r1, s1) = (r1, s1) := by rw [← hb]; exact fix_clock_evaluate cs body
    simp only [hb, hf, wordSemSTOP]
    split <;> simp_all

theorem function_loop_cost_cut_none (names : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (exitNames : WordLangNumSetHOL) (s : WordSemStateFiniteExact 64 C F)
    (hcs : cutState (names, .ln) s = none) :
    wordFunctionExecutionCost price function (.loop names body exitNames) s =
      price function (.loop names body exitNames) s := by
  rw [wordFunctionExecutionCost]
  split
  · rfl
  · rename_i cs' h; rw [hcs] at h; cases h

end Unfold

/-- Code is constant along non-installing runs over a non-installing table. -/
theorem run_code {C F : Type} (prog : WordLangProgHOL (BitVec 64)) (state : WordSemStateFiniteExact 64 C F)
    (free : noInstallSubprogsHOL prog = true) (codeFree : WordProps.noInstallCode state.code) :
    (evaluate prog state).2.code = state.code :=
  code_evaluate prog state free codeFree

/-- Sequence over the two tables. -/
theorem colourIndexed_seq {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (col : Nat → Nat → Nat)
    (function : Nat) (f : Nat → Nat)
    (sourceFree : WordProps.noInstallCode source) (targetFree : WordProps.noInstallCode target)
    (leafPrice : ∀ p, TP (applyColour f p) ≤ SP function p)
    (permuteCost : IndexedPermuteCost C F SP) (first second : WordLangProgHOL (BitVec 64))
    (ihFirst : ColourIndexedGoal C F TP SP source target col function f first)
    (ihSecond : ColourIndexedGoal C F TP SP source target col function f second) :
    ColourIndexedGoal C F TP SP source target col function f (.seq first second) := by
  rintro st cst live lt calleeIH free sourceCode targetCode ⟨hc, hs, hl⟩
  have parts : noInstallSubprogsHOL first = true ∧ noInstallSubprogsHOL second = true := by
    simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] using free
  obtain ⟨p1, hp1⟩ := ihFirst st cst (getLive second live lt) lt calleeIH parts.1 sourceCode targetCode
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
  have head := leafPrice (.seq first second)
  rw [targetSeq] at head
  have middleCode : s1.code = source := by
    have h := run_code first {st with permute := p1} parts.1 (by rw [← sourceCode] at sourceFree; exact sourceFree)
    rw [he1] at h
    exact h.trans sourceCode
  have targetMiddleCode : cs1.code = target := by
    have h := run_code (applyColour f first) cst (noInstall_applyColour f first parts.1)
      (by rw [targetCode]; exact targetFree)
    rw [hec1] at h
    exact h.trans targetCode
  cases r1 with
  | some result =>
    refine ⟨p1, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [targetSeq, evaluate, fix_clock_evaluate, he1, evaluate, fix_clock_evaluate, hec1]
    · rw [targetSeq, evaluate, fix_clock_evaluate, he1, evaluate, fix_clock_evaluate, hec1]
      exact frame1
    · rw [targetSeq, evaluate, fix_clock_evaluate, he1, evaluate, fix_clock_evaluate, hec1]
      cases result <;> exact locals1
    · rw [targetSeq, wordExecutionCost_seq, wordFunctionExecutionCost_seq, hec1, he1]
      simp only [Nat.add_zero]
      exact Nat.add_le_add head cost1
  | none =>
    have clocks := evaluate_clock first {st with permute := p1} none s1 he1
    obtain ⟨p2, hp2⟩ := ihSecond s1 cs1 live lt
      (calleeIH.mono (by right; exact ⟨clocks.2, clocks.1⟩)) parts.2 middleCode targetMiddleCode
      ⟨hc.2.1, frame1, locals1⟩
    dsimp only at hp2
    obtain ⟨p0, run0, cost0⟩ := permuteCost function first {st with permute := p1} p2
      (by rw [he1]; simp)
    rw [he1] at run0
    have run0' : evaluate first {st with permute := p0} = (none, {s1 with permute := p2}) := run0
    have cost0' : wordFunctionExecutionCost (fun l p _ => SP l p) function first {st with permute := p0} =
        wordFunctionExecutionCost (fun l p _ => SP l p) function first {st with permute := p1} := cost0
    refine ⟨p0, ?_⟩
    dsimp only
    rw [targetSeq, evaluate, fix_clock_evaluate, run0', evaluate, fix_clock_evaluate, hec1]
    dsimp only
    rcases hp2 with bad | ⟨same2, frame2, locals2, cost2⟩
    · exact Or.inl bad
    · refine Or.inr ⟨same2, frame2, locals2, ?_⟩
      rw [wordExecutionCost_seq, wordFunctionExecutionCost_seq, hec1, run0']
      simp only
      rw [cost0']
      omega

/-- Conditional over the two tables. -/
theorem colourIndexed_ite {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (col : Nat → Nat → Nat)
    (function : Nat) (f : Nat → Nat)
    (leafPrice : ∀ p, TP (applyColour f p) ≤ SP function p)
    (cmp : Cmp) (left : Nat) (right : WordRegImm (BitVec 64)) (yes no : WordLangProgHOL (BitVec 64))
    (ihYes : ColourIndexedGoal C F TP SP source target col function f yes)
    (ihNo : ColourIndexedGoal C F TP SP source target col function f no) :
    ColourIndexedGoal C F TP SP source target col function f (.ite cmp left right yes no) := by
  rintro st cst live lt calleeIH free sourceCode targetCode ⟨hc, hs, hl⟩
  have parts : noInstallSubprogsHOL yes = true ∧ noInstallSubprogsHOL no = true := by
    simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] using free
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
  have stuck : (evaluate (.ite cmp left right yes no) st).1 = some .error →
      ColourIndexedPost TP SP function f (.ite cmp left right yes no) live lt st cst :=
    fun stop => ⟨st.permute, Or.inl stop⟩
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
            (armIH : ColourIndexedGoal C F TP SP source target col function f arm)
            (armFree : noInstallSubprogsHOL arm = true)
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
              wordFunctionExecutionCost (fun l p _ => SP l p) function (.ite cmp left right yes no) s =
                SP function (.ite cmp left right yes no) +
                  wordFunctionExecutionCost (fun l p _ => SP l p) function arm s)
            (targetCost : wordExecutionCost (fun p _ => TP p)
              (applyColour f (.ite cmp left right yes no)) cst =
                TP (applyColour f (.ite cmp left right yes no)) +
                  wordExecutionCost (fun p _ => TP p) (applyColour f arm) cst),
            ColourIndexedPost TP SP function f (.ite cmp left right yes no) live lt st cst := by
          intro arm armIH armFree armLive armOk sourceSel targetSel sourceCost targetCost
          obtain ⟨perm, hp⟩ := armIH st cst live lt calleeIH armFree sourceCode targetCode
            ⟨armOk, hs, slrMono hl (fun k hk => hm k (armLive k hk))⟩
          refine ⟨perm, ?_⟩
          dsimp only at hp ⊢
          rw [sourceSel _ (by rw [hv]; exact hx) (by rw [hi]; exact hy), targetSel,
            sourceCost _ (by rw [hv]; exact hx) (by rw [hi]; exact hy), targetCost]
          rcases hp with bad | ⟨same, frame, locals, cost⟩
          · exact Or.inl bad
          · exact Or.inr ⟨same, frame, locals, Nat.add_le_add (leafPrice _) cost⟩
        cases decision with
        | true =>
          apply branch yes ihYes parts.1 (fun k hk => (sptDomain_uni _ _ k).mpr (Or.inl hk)) hc.2.1
          · intro s gx gy; rw [evaluate, gx, gy]; simp only [hw]
          · rw [targetIte, evaluate, hcx, hcy]; simp only [hw]
          · intro s gx gy; rw [wordFunctionExecutionCost_ite, gx, gy]; simp only [hw]
          · rw [targetIte, wordExecutionCost_ite, hcx, hcy]; simp only [hw]
        | false =>
          apply branch no ihNo parts.2 (fun k hk => (sptDomain_uni _ _ k).mpr (Or.inr hk)) hc.2.2
          · intro s gx gy; rw [evaluate, gx, gy]; simp only [hw]
          · rw [targetIte, evaluate, hcx, hcy]; simp only [hw]
          · intro s gx gy; rw [wordFunctionExecutionCost_ite, gx, gy]; simp only [hw]
          · rw [targetIte, wordExecutionCost_ite, hcx, hcy]; simp only [hw]

/-- MustTerminate over the two tables. -/
theorem colourIndexed_mustTerminate {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (col : Nat → Nat → Nat)
    (function : Nat) (f : Nat → Nat)
    (leafPrice : ∀ p, TP (applyColour f p) ≤ SP function p) (body : WordLangProgHOL (BitVec 64))
    (ih : ColourIndexedGoal C F TP SP source target col function f body) :
    ColourIndexedGoal C F TP SP source target col function f (.mustTerminate body) := by
  rintro st cst live lt calleeIH free sourceCode targetCode ⟨hc, hs, hl⟩
  have bodyFree : noInstallSubprogsHOL body = true := by
    simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.true_and] using free
  have hdep : cst.termdep = st.termdep := by simp_all [wordStateEqRel]
  by_cases hz : st.termdep = 0
  · refine ⟨st.permute, Or.inl ?_⟩
    rw [evaluate]
    simp [hz]
  · let s := {st with clock := wordSemMustTerminateLimit 64, termdep := st.termdep - 1}
    let cs := {cst with clock := wordSemMustTerminateLimit 64, termdep := cst.termdep - 1}
    have hsc : wordStateEqRel s {cs with code := s.code} := by simp_all [s, cs, wordStateEqRel]
    obtain ⟨perm, hp⟩ := ih s cs live lt (calleeIH.mono (by left; show st.termdep - 1 < st.termdep; omega))
      bodyFree sourceCode targetCode
      ⟨hc, hsc, by simpa only [getLive] using hl⟩
    rcases he : evaluate body {s with permute := perm} with ⟨res, rs⟩
    dsimp only at hp
    rw [he] at hp
    dsimp only at hp
    refine ⟨perm, ?_⟩
    have hein : evaluate body
        { { st with permute := perm } with clock := wordSemMustTerminateLimit 64, termdep := st.termdep - 1 } =
          (res, rs) := he
    have sourceCost : wordFunctionExecutionCost (fun l p _ => SP l p) function (.mustTerminate body)
        {st with permute := perm} = SP function (.mustTerminate body) +
          wordFunctionExecutionCost (fun l p _ => SP l p) function body {s with permute := perm} := by
      rw [wordFunctionExecutionCost_mustTerminate]
      simp only [hz, if_false]
      rfl
    have targetCost : wordExecutionCost (fun p _ => TP p) (applyColour f (.mustTerminate body))
        cst = TP (applyColour f (.mustTerminate body)) +
          wordExecutionCost (fun p _ => TP p) (applyColour f body) cs := by
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
    have costBound := Nat.add_le_add (leafPrice (.mustTerminate body)) cost
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

#print axioms wordFunctionExecutionCost_ite
#print axioms function_loop_cost_clause
#print axioms colourIndexed_seq
#print axioms colourIndexed_ite
#print axioms colourIndexed_mustTerminate
end InitECandidate.Runtime.FineCost
