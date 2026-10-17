import InitECandidate.Runtime.RlpListCountLoopCountMonotone
import InitECandidate.Runtime.RlpListCountNormalTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpListCount_loop_normal_count_strict {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : RlpListCountLoopWitness state pointer length scratch frame ceiling)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (budget : (length.toNat - valid.offset.toNat) * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock)
    (enabled : valid.offset.toNat < length.toNat)
    (count : BitVec 64) (atCount : post.locals.lookup (ofString "count") = some (.val (.word count)))
    (run : evaluateHOLFiniteState state rlpListCountLoop = (none,post)) :
    valid.count.toNat < count.toNat := by
  let cost := (2 * length.toNat + 1) * 15 + 19
  have rankPositive : 0 < length.toNat - valid.offset.toNat := by omega
  have firstTicks : cost ≤ state.clock := by
    exact Nat.le_trans (Nat.le_mul_of_pos_left cost rankPositive) budget
  have ticks : (2 * length.toNat + 1) * 15 + 18 ≤ (decClockHOLFinite state).clock := by
    change (2 * length.toNat + 1) * 15 + 18 ≤ state.clock - 1
    dsimp [cost] at firstTicks
    omega
  obtain ⟨middle,step,tail⟩ := rlpListCount_loop_normal_tail state post valid.offset length
    valid.offsetLocal valid.lengthLocal enabled run
  obtain ⟨next,decreases⟩ := rlpListCount_loop_witness_step (decClockHOLFinite state) middle
    pointer length scratch frame ceiling inputLimit valid.decClock noWrap lengthBound limitBound
    orderedFrame framePositive scratchBelow ticks step
  have bounded := evaluate_rlpListCount_step_bounded (decClockHOLFinite state) pointer length valid.offset scratch frame ceiling inputLimit
    valid.pointerLocal valid.lengthLocal valid.offsetLocal valid.offsetBound noWrap lengthBound limitBound
    valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena ticks
  rw [step] at bounded
  dsimp only at bounded
  have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) rlpListCountStep
  rw [step] at remaining
  have fixed : (fixClockHOLFinite (decClockHOLFinite state) ((none : Option (PanSemResultExact 64)),middle)).2 = middle := by
    simp [fixClockHOLFinite,Nat.not_lt.mpr remaining]
  rw [fixed] at tail
  have nextBudget : (length.toNat - next.offset.toNat) * cost ≤ middle.clock := by
    have smaller : (length.toNat - next.offset.toNat) + 1 ≤ length.toNat - valid.offset.toNat := by
      have reduced : length.toNat - next.offset.toNat < length.toNat - valid.offset.toNat := decreases
      omega
    have products := Nat.mul_le_mul_right cost smaller
    have positiveClock : 0 < state.clock := by dsimp [cost] at firstTicks; omega
    have firstCost := bounded.1
    change state.clock - 1 ≤ middle.clock + ((2 * length.toNat + 1) * 15 + 18) at firstCost
    dsimp [cost] at products ⊢
    rw [Nat.add_mul] at products
    omega
  obtain ⟨result,output,actual,_,_,_,done,_⟩ := evaluate_rlpListCount_loop_count_monotone_bounded
    middle pointer length scratch frame ceiling inputLimit next noWrap lengthBound limitBound orderedFrame framePositive scratchBelow nextBudget
  have equal := Prod.mk.inj (actual.symm.trans tail)
  obtain ⟨finalCount,_,finalLocal,_,_,_,monotone⟩ := done equal.1
  have sameCount : finalCount = count := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj
    (finalLocal.symm.trans (by rw [equal.2]; exact atCount))))
  obtain ⟨_,_,_,_,_,_,increment⟩ := rlpListCount_step_consumed (decClockHOLFinite state) middle
    pointer length valid.offset valid.count valid.pointerLocal valid.lengthLocal valid.offsetLocal valid.countLocal valid.code
    (by change 13 ≤ state.clock - 1; dsimp [cost] at firstTicks; omega) step
  have nextCount : next.count = valid.count + 1 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (next.countLocal.symm.trans increment)))
  have incrementNat : (valid.count + 1).toNat = valid.count.toNat + 1 :=
    BitVec.toNat_add_of_lt (by have a := valid.countBound; have b := length.isLt; change valid.count.toNat + 1 < 2^64; omega)
  rw [sameCount,nextCount,incrementNat] at monotone
  omega

#print axioms rlpListCount_loop_normal_count_strict
end InitECandidate.Runtime
