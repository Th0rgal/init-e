import InitECandidate.Runtime.RlpCountFillStepInputInvariant
import InitECandidate.Runtime.RlpCountFillLoopDone
import InitECandidate.Runtime.RlpListCountLoopGuardAgreement
import InitECandidate.Runtime.RlpSlicesMemoryInvariant
import InitECandidate.Runtime.RlpSlicesNormalTail
import InitECandidate.Runtime.RlpListCountNormalTail
import InitECandidate.Runtime.RlpSliceInputPrefixClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpCountFill_loop_input_prefix {F : Type}
    (pointer length scratch frame array sliceCount : BitVec 64) (ceiling inputLimit : Nat)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputAligned : pointer.toNat % 8 = 0) (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (checkedFinal uncheckedFinal : PanSemStateFiniteExact 64 F)
    (finalCount : checkedFinal.locals.lookup (ofString "count") = some (.val (.word sliceCount)))
    (checked unchecked : PanSemStateFiniteExact 64 F)
    (vc : RlpListCountLoopWitness checked pointer length scratch frame ceiling)
    (vu : RlpSlicesMemoryWitness unchecked pointer sliceCount array)
    (offsetMatch : vu.control.offset = vc.offset) (countMatch : vu.control.index = vc.count)
    (filled : RlpSliceInputPrefix unchecked array pointer length vu.control.index.toNat)
    (reads : ∀ byteOffset : Nat, byteOffset < length.toNat →
      @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs (fun a => Classical.propDecidable (checked.memaddrs a)) checked.be (pointer + BitVec.ofNat 64 byteOffset) =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs (fun a => Classical.propDecidable (unchecked.memaddrs a)) unchecked.be (pointer + BitVec.ofNat 64 byteOffset))
    (checkedBudget : (length.toNat - vc.offset.toNat) * ((2 * length.toNat + 1) * 15 + 19) ≤ checked.clock)
    (uncheckedBudget : (sliceCount.toNat - vu.control.index.toNat) * 12 ≤ unchecked.clock)
    (checkedRun : evaluateHOLFiniteState checked rlpListCountLoop = (none,checkedFinal))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpSlicesLoop = (none,uncheckedFinal)) :
    RlpSliceInputPrefix uncheckedFinal array pointer length sliceCount.toNat := by
  have main : ∀ ticks : Nat, ∀
    (checked unchecked : PanSemStateFiniteExact 64 F)
    (vc : RlpListCountLoopWitness checked pointer length scratch frame ceiling)
    (vu : RlpSlicesMemoryWitness unchecked pointer sliceCount array)
    (offsetMatch : vu.control.offset = vc.offset) (countMatch : vu.control.index = vc.count)
    (filled : RlpSliceInputPrefix unchecked array pointer length vu.control.index.toNat)
    (reads : ∀ byteOffset : Nat, byteOffset < length.toNat →
      @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs (fun a => Classical.propDecidable (checked.memaddrs a)) checked.be (pointer + BitVec.ofNat 64 byteOffset) =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs (fun a => Classical.propDecidable (unchecked.memaddrs a)) unchecked.be (pointer + BitVec.ofNat 64 byteOffset))
    (checkedBudget : (length.toNat - vc.offset.toNat) * ((2 * length.toNat + 1) * 15 + 19) ≤ checked.clock)
    (uncheckedBudget : (sliceCount.toNat - vu.control.index.toNat) * 12 ≤ unchecked.clock)
    (checkedRun : evaluateHOLFiniteState checked rlpListCountLoop = (none,checkedFinal))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpSlicesLoop = (none,uncheckedFinal)), checked.clock = ticks → RlpSliceInputPrefix uncheckedFinal array pointer length sliceCount.toNat := by
    intro ticks
    induction ticks using Nat.strong_induction_on with
    | h ticks ih =>
      intro checked unchecked vc vu offsetMatch countMatch filled reads checkedBudget uncheckedBudget checkedRun uncheckedRun clockEq
      by_cases inside : vc.offset.toNat < length.toNat
      · have indexInside : vu.control.index.toNat < sliceCount.toNat := by
          rw [countMatch]
          exact (rlpListCount_loop_guard_matches_final_count checked checkedFinal pointer length scratch frame ceiling inputLimit
            vc noWrap lengthBound limitBound orderedFrame framePositive scratchBelow checkedBudget sliceCount finalCount checkedRun).mp inside
        let cost := (2 * length.toNat + 1) * 15 + 19
        have firstBudget : cost ≤ checked.clock :=
          Nat.le_trans (Nat.le_mul_of_pos_left _ (by omega)) checkedBudget
        have checkedTicks : (2 * length.toNat + 1) * 15 + 18 ≤ (decClockHOLFinite checked).clock := by
          change (2 * length.toNat + 1) * 15 + 18 ≤ checked.clock - 1
          dsimp [cost] at firstBudget
          omega
        have fillBudget : 12 ≤ unchecked.clock :=
          Nat.le_trans (Nat.le_mul_of_pos_left _ (by omega)) uncheckedBudget
        have uncheckedTicks : 11 ≤ (decClockHOLFinite unchecked).clock := by change 11 ≤ unchecked.clock - 1; omega
        obtain ⟨cm,cs,ct⟩ := rlpListCount_loop_normal_tail checked checkedFinal vc.offset length vc.offsetLocal vc.lengthLocal inside checkedRun
        obtain ⟨um,us,ut⟩ := rlpSlices_loop_normal_tail unchecked uncheckedFinal vu.control.index sliceCount
          vu.control.indexLocal vu.control.countLocal indexInside uncheckedRun
        have cb := evaluate_rlpListCount_step_bounded (decClockHOLFinite checked) pointer length vc.offset scratch frame ceiling inputLimit
          vc.pointerLocal vc.lengthLocal vc.offsetLocal vc.offsetBound noWrap lengthBound limitBound
          vc.scratchGlobal vc.frameGlobal vc.code orderedFrame framePositive scratchBelow vc.arena checkedTicks
        have ub := evaluate_rlpSlices_step_bounded (decClockHOLFinite unchecked) pointer vu.control.offset
          vu.control.pointerLocal vu.control.offsetLocal vu.control.code uncheckedTicks
        rw [cs] at cb
        rw [us] at ub
        dsimp only at cb ub
        have cf : (fixClockHOLFinite (decClockHOLFinite checked) ((none : Option (PanSemResultExact 64)),cm)).2 = cm := by
          simp [fixClockHOLFinite,Nat.not_lt.mpr cb.2.1]
        have uf : (fixClockHOLFinite (decClockHOLFinite unchecked) ((none : Option (PanSemResultExact 64)),um)).2 = um := by
          simp [fixClockHOLFinite,Nat.not_lt.mpr ub.2.1]
        rw [cf] at ct
        rw [uf] at ut
        obtain ⟨nc,decreases⟩ := rlpListCount_loop_witness_step (decClockHOLFinite checked) cm pointer length scratch frame ceiling inputLimit
          vc.decClock noWrap lengthBound limitBound orderedFrame framePositive scratchBelow checkedTicks cs
        obtain ⟨nu,_⟩ := rlpSlices_memory_witness_step (decClockHOLFinite unchecked) um pointer sliceCount array vu.decClock
          (by rw [rlpSlices_rank_eq _ pointer sliceCount vu.control.decClock]; change 0 < sliceCount.toNat - vu.control.index.toNat; omega) uncheckedTicks us
        have uncheckedOffset : unchecked.locals.lookup (ofString "off") = some (.val (.word vc.offset)) := by
          simpa only [offsetMatch] using vu.control.offsetLocal
        obtain ⟨nextFilled,consumed,co,uo,positive,fits,natural,nextReads⟩ :=
          rlpCountFill_step_retains_input_invariant (decClockHOLFinite checked) (decClockHOLFinite unchecked) cm um
            pointer length vc.offset vc.count vu.control.index vc.pointerLocal vc.lengthLocal vc.offsetLocal vc.countLocal
            vu.control.pointerLocal uncheckedOffset vu.control.indexLocal array vu.arrayLocal (vu.domain _ indexInside).1 (vu.domain _ indexInside).2
            sliceCount indexInside vu.fits (filled.dec_clock unchecked array pointer length _) noWrap inside vc.code vu.control.code
            (by change 13 ≤ checked.clock - 1; dsimp [cost] at firstBudget; omega) uncheckedTicks reads
            scratch frame ceiling inputLimit lengthBound limitBound vc.scratchGlobal vc.frameGlobal orderedFrame framePositive
            scratchBelow vc.arena checkedTicks inputBeforeFrame inputAligned inputBeforeArray cs us
        have ncOffset : nc.offset = vc.offset + consumed := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nc.offsetLocal.symm.trans co)))
        have nuOffset : nu.control.offset = vc.offset + consumed := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nu.control.offsetLocal.symm.trans uo)))
        obtain ⟨_,_,_,_,_,_,incrementC⟩ := rlpListCount_step_consumed (decClockHOLFinite checked) cm pointer length vc.offset vc.count
          vc.pointerLocal vc.lengthLocal vc.offsetLocal vc.countLocal vc.code (by change 13 ≤ checked.clock - 1; dsimp [cost] at firstBudget; omega) cs
        obtain ⟨_,_,_,_,incrementU⟩ := rlpSlices_step_consumed (decClockHOLFinite unchecked) um pointer vu.control.offset vu.control.index
          vu.control.pointerLocal vu.control.offsetLocal vu.control.indexLocal vu.control.code us
        have ncCount : nc.count = vc.count + 1 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nc.countLocal.symm.trans incrementC)))
        have nuIndex : nu.control.index = vu.control.index + 1 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nu.control.indexLocal.symm.trans incrementU)))
        have nextCB : (length.toNat - nc.offset.toNat) * cost ≤ cm.clock := by
          have smaller : (length.toNat - nc.offset.toNat) + 1 ≤ length.toNat - vc.offset.toNat := by
            have reduced : length.toNat - nc.offset.toNat < length.toNat - vc.offset.toNat := decreases
            omega
          have products := Nat.mul_le_mul_right cost smaller
          have firstCost := cb.1
          change checked.clock - 1 ≤ cm.clock + ((2 * length.toNat + 1) * 15 + 18) at firstCost
          dsimp [cost] at products ⊢ firstBudget
          rw [Nat.add_mul] at products
          omega
        have nextUB : (sliceCount.toNat - nu.control.index.toNat) * 12 ≤ um.clock := by
          have incrementNat : (vu.control.index + 1).toNat = vu.control.index.toNat + 1 :=
            BitVec.toNat_add_of_lt (by have bound := sliceCount.isLt; change vu.control.index.toNat + 1 < 2^64; omega)
          rw [nuIndex,incrementNat]
          have products : (sliceCount.toNat - (vu.control.index.toNat + 1)) * 12 + 12 = (sliceCount.toNat - vu.control.index.toNat) * 12 := by omega
          have firstCost := ub.1
          change unchecked.clock - 1 ≤ um.clock + 11 at firstCost
          omega
        have smallerClock : cm.clock < ticks := by
          have remaining := cb.2.1
          change cm.clock ≤ checked.clock - 1 at remaining
          dsimp [cost] at firstBudget
          omega
        apply ih cm.clock smallerClock cm um nc nu
        · exact nuOffset.trans ncOffset.symm
        · rw [nuIndex,ncCount,countMatch]
        · simpa only [nuIndex] using nextFilled
        · exact nextReads
        · exact nextCB
        · exact nextUB
        · exact ct
        · exact ut
        · rfl
      · have ended : vc.offset = length := by
          apply BitVec.eq_of_toNat_eq
          have bounded := vc.offsetBound
          omega
        have co : checked.locals.lookup (ofString "off") = some (.val (.word length)) := by simpa only [ended] using vc.offsetLocal
        have ui : unchecked.locals.lookup (ofString "i") = some (.val (.word vc.count)) := by simpa only [countMatch] using vu.control.indexLocal
        exact (rlpCountFill_loop_done checked unchecked checkedFinal uncheckedFinal pointer length array vc.count sliceCount
          co vc.lengthLocal vc.countLocal finalCount ui vu.control.countLocal (by simpa only [countMatch] using filled) checkedRun uncheckedRun).2.2
  exact main checked.clock checked unchecked vc vu offsetMatch countMatch filled reads checkedBudget uncheckedBudget checkedRun uncheckedRun rfl

#print axioms rlpCountFill_loop_input_prefix
end InitECandidate.Runtime
