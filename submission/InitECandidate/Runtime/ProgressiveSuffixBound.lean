import InitECandidate.Runtime.ProgressiveSuffixSource
import InitECandidate.Runtime.Sha256PairBound
import InitECandidate.Runtime.VmFn_heap_release
import InitECandidate.Runtime.MerklePaddingBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressiveFold_tail_bounded : ProgBounded progressiveFoldTail 136 :=
  ProgBounded.call sha256Pair_funBounded _ _

theorem progressiveFinish_bounded : ProgBounded (progressiveAt 9) 17 := by
  rw [source_progressive_finish]
  apply ProgBounded.weaken
  · exact ProgBounded.seq (memcpy_const_progBounded _ _ 32 (by decide))
      (ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))
  · decide

def progressiveFoldCost : Nat := (4 * 134217712) * 137

theorem runBounded_progressive_fold {F : Type} (state : PanSemStateFiniteExact 64 F)
    (k : BitVec 64) (atK : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (small : k.toNat ≤ 4 * 134217712) (code : state.code = originalRuntimeCode)
    (budget : progressiveFoldCost ≤ state.clock) :
    RunBounded state progressiveFoldLoop progressiveFoldCost := by
  have loop := countdown_ranked (ofString "k") progressiveFoldTail 136 progressiveFold_tail_bounded
    (by decide) (by decide) (by decide) (4 * 134217712) state code ⟨k,atK,small⟩ budget
  exact ⟨loop.1,loop.2.1,loop.2.2.1⟩

theorem runBounded_progressive_fold_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (k : BitVec 64) (atK : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (small : k.toNat ≤ 4 * 134217712) (code : state.code = originalRuntimeCode)
    (budget : progressiveFoldCost + 17 ≤ state.clock) :
    RunBounded state (progressiveAt 8) (progressiveFoldCost + 17) := by
  rw [source_progressive_fold]
  refine RunBounded.seq (runBounded_progressive_fold state k atK small code (by omega)) budget ?_
  intro next normal nextCode remaining
  exact RunBounded.ofProg progressiveFinish_bounded (nextCode.trans code) remaining

theorem runBounded_progressive_zero_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (k : BitVec 64) (atK : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (small : k.toNat ≤ 4 * 134217712) (code : state.code = originalRuntimeCode)
    (budget : 16 + (progressiveFoldCost + 17) ≤ state.clock) :
    RunBounded state (progressiveAt 7) (16 + (progressiveFoldCost + 17)) := by
  rw [source_progressive_zero]
  refine RunBounded.seq (RunBounded.ofProg (memzero_const_progBounded _ 32 (by decide)) code (by omega)) budget ?_
  intro next normal nextCode remaining
  have frame := evaluate_avoidsLocal_flowing (ofString "k")
    (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "acc"),.const 32])
    (by decide) state (by rw [normal]; exact Or.inl rfl)
  rw [normal] at frame
  exact runBounded_progressive_fold_suffix next k (frame.trans atK) small (nextCode.trans code) remaining

#print axioms progressiveFold_tail_bounded
#print axioms progressiveFinish_bounded
#print axioms runBounded_progressive_fold
#print axioms runBounded_progressive_fold_suffix
#print axioms runBounded_progressive_zero_suffix
end InitECandidate.Runtime
