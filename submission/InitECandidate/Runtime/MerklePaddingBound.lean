import InitECandidate.Runtime.MerklePaddingSource
import InitECandidate.Runtime.Sha256PairBound
import InitECandidate.Runtime.LocalBoundLoop
import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.VmFn_heap_release
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merklePadding_counted : CountedBody (ofString "d") 1 merklePaddingBody (136 + 0) := by
  rw [source_merklePadding_body]
  exact CountedBody.seq _ (ProgBounded.call sha256Pair_funBounded _ _)
    (by decide) (by decide) CountedBody.incr

theorem merkleFinish_bounded : ProgBounded (merkleizeAt 13) 17 := by
  rw [source_merkleFinish]
  apply ProgBounded.weaken
  · exact ProgBounded.seq (memcpy_const_progBounded _ _ 32 (by decide))
      (ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))
  · decide

def merklePaddingCost : Nat := 63 * 137

theorem runBounded_merklePadding {F : Type} (state : PanSemStateFiniteExact 64 F)
    (d target : BitVec 64)
    (counter : state.locals.lookup (ofString "d") = some (.val (.word d)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (small : d.toNat < 2 ^ 63) (targetBound : target.toNat ≤ 63)
    (code : state.code = originalRuntimeCode) (budget : merklePaddingCost ≤ state.clock) :
    RunBounded state merklePaddingLoop merklePaddingCost := by
  have loop := localBoundWhile_run (ofString "d") (ofString "target") 1 target
    (LocalBoundTest.below .less (Or.inl rfl)) (by change target.toNat + 1 < 2 ^ 63; omega)
    (by decide) merklePadding_counted (by decide) (by decide) state code d counter limit small
    (by simp; change _ ≤ state.clock; unfold merklePaddingCost at budget; omega)
  have raw : RunBounded state merklePaddingLoop ((target.toNat - d.toNat) * 137) := by
    exact ⟨by simpa [merklePaddingLoop] using loop.1,by simpa [merklePaddingLoop] using loop.2.1,
      by simpa [merklePaddingLoop] using loop.2.2.1⟩
  exact raw.weaken (by unfold merklePaddingCost; omega)

theorem runBounded_merklePaddingSuffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (d target : BitVec 64)
    (counter : state.locals.lookup (ofString "d") = some (.val (.word d)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (small : d.toNat < 2 ^ 63) (targetBound : target.toNat ≤ 63)
    (code : state.code = originalRuntimeCode) (budget : merklePaddingCost + 17 ≤ state.clock) :
    RunBounded state (merkleizeAt 12) (merklePaddingCost + 17) := by
  rw [source_merklePadding]
  refine RunBounded.seq (runBounded_merklePadding state d target counter limit small targetBound code (by omega)) budget ?_
  intro next _ nextCode remaining
  exact RunBounded.ofProg merkleFinish_bounded (nextCode.trans code) remaining

#print axioms merklePadding_counted
#print axioms merkleFinish_bounded
#print axioms runBounded_merklePadding
#print axioms runBounded_merklePaddingSuffix
end InitECandidate.Runtime
