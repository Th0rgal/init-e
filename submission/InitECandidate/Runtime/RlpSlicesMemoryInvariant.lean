import InitECandidate.Runtime.RlpSlicesPrefix
import InitECandidate.Runtime.RlpSlicesArrayLocal
import InitECandidate.Runtime.RlpSlicesLoopInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original slice loop's control witness together with its concrete
allocated-array domain and all entries already filled. -/
structure RlpSlicesMemoryWitness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer count array : BitVec 64) where
  control : RlpSlicesLoopWitness state pointer count
  arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array))
  fits : array.toNat + count.toNat * 16 ≤ 2^64
  domain : ∀ slot : BitVec 64, slot.toNat < count.toNat →
    state.memaddrs (array + slot * 16#64) ∧ state.memaddrs (array + slot * 16#64 + 8#64)
  filled : RlpSlicePrefix state array control.index.toNat

/-- Actual normal iterations preserve the combined control/memory invariant
and strictly lower the remaining-slice rank. -/
theorem rlpSlices_memory_witness_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count array : BitVec 64) (valid : RlpSlicesMemoryWitness state pointer count array)
    (enabled : 0 < rlpSlicesRank count state) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    ∃ _next : RlpSlicesMemoryWitness post pointer count array,
      rlpSlicesRank count post < rlpSlicesRank count state := by
  let control := valid.control
  have inside : control.index.toNat < count.toNat := by
    rw [rlpSlices_rank_eq state pointer count control] at enabled
    omega
  obtain ⟨offset,offsetLocal,indexLocal,countLocal,pointerLocal,indexBound,decreases⟩ :=
    rlpSlices_step_normal_invariant state post pointer control.offset control.index count control.pointerLocal control.offsetLocal
      control.indexLocal control.countLocal inside control.code run
  have metadata := evaluateHOLFiniteState_metadata state rlpSlicesStep
  rw [run] at metadata
  dsimp only at metadata
  let nextControl : RlpSlicesLoopWitness post pointer count :=
    ⟨offset,control.index+1,pointerLocal,countLocal,offsetLocal,indexLocal,indexBound,metadata.1.trans control.code⟩
  have nextArray := rlpSlices_step_array_local state post pointer control.offset control.index array
    control.pointerLocal control.offsetLocal control.indexLocal valid.arrayLocal control.code run
  have nextPrefix := rlpSlices_step_extends_prefix state post array control.index pointer control.offset
    valid.arrayLocal control.indexLocal control.pointerLocal control.offsetLocal (valid.domain _ inside).1 (valid.domain _ inside).2
    count inside valid.fits valid.filled control.code ticks run
  have nextDomain : ∀ slot : BitVec 64, slot.toNat < count.toNat →
      post.memaddrs (array + slot * 16#64) ∧ post.memaddrs (array + slot * 16#64 + 8#64) := by
    intro slot bounded
    rw [metadata.2.1]
    exact valid.domain slot bounded
  let next : RlpSlicesMemoryWitness post pointer count array :=
    ⟨nextControl,nextArray,valid.fits,nextDomain,nextPrefix⟩
  refine ⟨next,?_⟩
  rw [rlpSlices_rank_eq post pointer count nextControl,rlpSlices_rank_eq state pointer count control]
  exact decreases

#print axioms rlpSlices_memory_witness_step
end InitECandidate.Runtime
