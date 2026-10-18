import InitECandidate.Runtime.SszSplitVarListLoop
import InitECandidate.Runtime.SszSplitCellsStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Loop invariant with slice-cell contents relative to the loop-entry memory. -/
def SszSplitInvB {σ : Type} (base : PanSemStateFiniteExact 64 σ) (p len first count arr : BitVec 64)
    (s : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ i prev : BitVec 64, ∃ L M, ∃ off : BitVec 64 → BitVec 64,
    s = {base with locals := L, memory := M, clock := s.clock} ∧
    SszSplitLocals L p len first count arr i prev ∧ i.toNat ≤ count.toNat ∧ count.toNat < 2 ^ 60 ∧
    (i = 0 → prev = first) ∧ (i ≠ 0 → prev = off (i - 1)) ∧
    SszSplitCellsOK base.memory base.memaddrs p len first arr off i M

theorem evaluate_sszSplitLoopB {σ : Type} (base : PanSemStateFiniteExact 64 σ) (p len first count arr : BitVec 64)
    (code : base.code = originalRuntimeCode)
    (s : PanSemStateFiniteExact 64 σ) (inv : SszSplitInvB base p len first count arr s)
    (ticks : sszSplitRank s * 2 ≤ s.clock) :
    ∃ result post, evaluateHOLFiniteState s sszSplitLoop = (result, post) ∧
      s.clock ≤ post.clock + sszSplitRank s * 2 ∧ post.clock ≤ s.clock ∧ result ≠ some .timeOut ∧
      (result = none → SszSplitInvB base p len first count arr post ∧ sszSplitRank post = 0) ∧
      (∀ value, result ≠ some (.returned value)) := by
  have guard : ∀ state, SszSplitInvB base p len first count arr state →
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .less (sszLocal "i") (sszLocal "count")) =
        some (.val (.word (if sszSplitRank state = 0 then 0 else 1))) := by
    rintro state ⟨i, prev, L, M, off, shape, ⟨_, _, _, hn, _, hi, _⟩, le, small, _⟩
    have si : state.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [shape]; exact hi
    have sn : state.locals.lookup (ofString "count") = some (.val (.word count)) := by rw [shape]; exact hn
    rw [sszSplit_rank_eq state i count si sn]
    by_cases zero : count.toNat - i.toNat = 0
    · simp [sszLocal, evalHOLFinite, evalHOLExact, si, sn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, zero]
      rw [if_pos (by omega)]; omega
    · simp [sszLocal, evalHOLFinite, evalHOLExact, si, sn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, zero]
      rw [if_pos (by omega)]; omega
  have entry : ∀ state, SszSplitInvB base p len first count arr state →
      SszSplitInvB base p len first count arr (decClockHOLFinite state) := by
    rintro state ⟨i, prev, L, M, off, shape, rest⟩
    exact ⟨i, prev, L, M, off, by rw [shape]; rfl, rest⟩
  have entryRank : ∀ state : PanSemStateFiniteExact 64 σ, sszSplitRank (decClockHOLFinite state) = sszSplitRank state := by
    intro state; rfl
  have step : ∀ state, SszSplitInvB base p len first count arr state → 0 < sszSplitRank state → 1 ≤ state.clock →
      ∃ post, state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧
        ((evaluateHOLFiniteState state sszSplitStep = (none,post) ∧ SszSplitInvB base p len first count arr post ∧
            sszSplitRank post < sszSplitRank state) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ value, result ≠ .returned value) ∧
           evaluateHOLFiniteState state sszSplitStep = (some result,post))) := by
    rintro state ⟨i, prev, L, M, off, shape, look, le, small, prevZero, prevOff, cells⟩ positive clock
    have stateLocals : state.locals = L := by rw [shape]
    have look' : SszSplitLocals state.locals p len first count arr i prev := by rw [stateLocals]; exact look
    have si := look'.2.2.2.2.2.1
    have sn := look'.2.2.2.1
    rw [sszSplit_rank_eq state i count si sn] at positive
    have stateCode : state.code = originalRuntimeCode := by rw [shape]; exact code
    have stateMem : state.memory = M := by rw [shape]
    have stateDom : state.memaddrs = base.memaddrs := by rw [shape]
    obtain ⟨c1, c2, outcome⟩ := sszSplitStep_outcome state p len first count arr i prev look' stateCode (by omega)
    cases run : evaluateHOLFiniteState state sszSplitStep with
    | mk result post =>
      rw [run] at c1 c2 outcome
      dsimp only at c1 c2 outcome
      refine ⟨post, c1, c2, ?_⟩
      rcases outcome with ⟨none_, o, _, o1, o2, o3, d1, d2, L', postShape, look2⟩ | ⟨x, hx, ab⟩
      · subst none_
        have succ : (i + 1).toNat = i.toNat + 1 := by
          rw [BitVec.toNat_add]; simp; omega
        have cells' := sszSplitCells_step base.memory M base.memaddrs p len first arr i prev o count off
          (by omega) small cells prevOff o1 o2 o3 (fun h => by rw [← stateDom]; exact d1 h)
          (by rw [← stateDom]; exact d2)
        refine Or.inl ⟨rfl, ⟨i + 1, o, L', sszSplitStepMemory state.memory arr p i o prev,
          fun k => if k = i then o else off k, ?_, look2, by omega, small, ?_, ?_, ?_⟩, ?_⟩
        · rw [postShape, shape]
        · intro z; have := congrArg BitVec.toNat z; simp at this; omega
        · intro _; simp
        · rw [stateMem]; exact cells'
        · have pi : post.locals.lookup (ofString "i") = some (.val (.word (i + 1))) := by
            rw [postShape]; exact look2.2.2.2.2.2.1
          have pn : post.locals.lookup (ofString "count") = some (.val (.word count)) := by
            rw [postShape]; exact look2.2.2.2.1
          rw [sszSplit_rank_eq post (i + 1) count pi pn, sszSplit_rank_eq state i count si sn, succ]
          omega
      · subst hx
        exact Or.inr ⟨x, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2, rfl⟩
  have result := evaluate_ranked_loop_exits_invariant _ sszSplitStep (SszSplitInvB base p len first count arr)
    sszSplitRank 1 guard entry entryRank step s inv (by simpa using ticks)
  simpa [sszSplitLoop] using result

#print axioms evaluate_sszSplitLoopB
end InitECandidate.Runtime
