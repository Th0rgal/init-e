import InitECandidate.Runtime.SszSplitVarListStepMain
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Loop states differ from a base state only in locals, memory and clock. -/
def SszSplitInv {σ : Type} (base : PanSemStateFiniteExact 64 σ) (p len first count arr : BitVec 64)
    (s : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ i prev : BitVec 64, ∃ L M, s = {base with locals := L, memory := M, clock := s.clock} ∧
    SszSplitLocals L p len first count arr i prev ∧ i.toNat ≤ count.toNat ∧ count.toNat < 2 ^ 62

def sszSplitRank {σ : Type} (s : PanSemStateFiniteExact 64 σ) : Nat :=
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "count") with
  | some (.val (.word i)), some (.val (.word n)) => n.toNat - i.toNat
  | _, _ => 0

theorem sszSplit_rank_eq {σ : Type} (s : PanSemStateFiniteExact 64 σ) (i n : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hn : s.locals.lookup (ofString "count") = some (.val (.word n))) :
    sszSplitRank s = n.toNat - i.toNat := by
  simp [sszSplitRank, hi, hn]

theorem evaluate_sszSplitLoop {σ : Type} (base : PanSemStateFiniteExact 64 σ) (p len first count arr : BitVec 64)
    (code : base.code = originalRuntimeCode)
    (s : PanSemStateFiniteExact 64 σ) (inv : SszSplitInv base p len first count arr s)
    (ticks : sszSplitRank s * 2 ≤ s.clock) :
    ∃ result post, evaluateHOLFiniteState s sszSplitLoop = (result, post) ∧
      s.clock ≤ post.clock + sszSplitRank s * 2 ∧ post.clock ≤ s.clock ∧ result ≠ some .timeOut ∧
      (result = none → SszSplitInv base p len first count arr post ∧ sszSplitRank post = 0) ∧
      (∀ value, result ≠ some (.returned value)) := by
  have guard : ∀ state, SszSplitInv base p len first count arr state →
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .less (sszLocal "i") (sszLocal "count")) =
        some (.val (.word (if sszSplitRank state = 0 then 0 else 1))) := by
    rintro state ⟨i, prev, L, M, shape, ⟨_, _, _, hn, _, hi, _⟩, le, small⟩
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
  have entry : ∀ state, SszSplitInv base p len first count arr state →
      SszSplitInv base p len first count arr (decClockHOLFinite state) := by
    rintro state ⟨i, prev, L, M, shape, rest⟩
    exact ⟨i, prev, L, M, by rw [shape]; rfl, rest⟩
  have entryRank : ∀ state : PanSemStateFiniteExact 64 σ, sszSplitRank (decClockHOLFinite state) = sszSplitRank state := by
    intro state; rfl
  have step : ∀ state, SszSplitInv base p len first count arr state → 0 < sszSplitRank state → 1 ≤ state.clock →
      ∃ post, state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧
        ((evaluateHOLFiniteState state sszSplitStep = (none,post) ∧ SszSplitInv base p len first count arr post ∧
            sszSplitRank post < sszSplitRank state) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ value, result ≠ .returned value) ∧
           evaluateHOLFiniteState state sszSplitStep = (some result,post))) := by
    rintro state ⟨i, prev, L, M, shape, look, le, small⟩ positive clock
    have stateLocals : state.locals = L := by rw [shape]
    have look' : SszSplitLocals state.locals p len first count arr i prev := by rw [stateLocals]; exact look
    have si := look'.2.2.2.2.2.1
    have sn := look'.2.2.2.1
    rw [sszSplit_rank_eq state i count si sn] at positive
    have stateCode : state.code = originalRuntimeCode := by rw [shape]; exact code
    obtain ⟨c1, c2, outcome⟩ := sszSplitStep_outcome state p len first count arr i prev look' stateCode (by omega)
    cases run : evaluateHOLFiniteState state sszSplitStep with
    | mk result post =>
      rw [run] at c1 c2 outcome
      dsimp only at c1 c2 outcome
      refine ⟨post, c1, c2, ?_⟩
      rcases outcome with ⟨none_, o, _, _, _, _, _, _, L', postShape, look2⟩ | ⟨x, hx, ab⟩
      · subst none_
        have succ : (i + 1).toNat = i.toNat + 1 := by
          rw [BitVec.toNat_add]; simp; omega
        refine Or.inl ⟨rfl, ⟨i + 1, o, L', sszSplitStepMemory state.memory arr p i o prev, ?_, look2, by omega, small⟩, ?_⟩
        · rw [postShape, shape]
        · have pi : post.locals.lookup (ofString "i") = some (.val (.word (i + 1))) := by
            rw [postShape]; exact look2.2.2.2.2.2.1
          have pn : post.locals.lookup (ofString "count") = some (.val (.word count)) := by
            rw [postShape]; exact look2.2.2.2.1
          rw [sszSplit_rank_eq post (i + 1) count pi pn, sszSplit_rank_eq state i count si sn, succ]
          omega
      · subst hx
        exact Or.inr ⟨x, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2, rfl⟩
  have result := evaluate_ranked_loop_exits_invariant _ sszSplitStep (SszSplitInv base p len first count arr)
    sszSplitRank 1 guard entry entryRank step s inv (by simpa using ticks)
  simpa [sszSplitLoop] using result

#print axioms evaluate_sszSplitLoop
end InitECandidate.Runtime
