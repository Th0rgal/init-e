import InitECandidate.Runtime.HeaderWithdrawalLoopWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Statement 46 (the payload-header withdrawal slice loop): the watched cell survives the loop, and
the statement's program is the loop followed by statement 47, so the tail's own window finishes it. -/
theorem payloadHeader46_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (I0 nwd pl slices heapBase w read X : BitVec 64) (H : Nat → BitVec 64)
    (readEq : read = pl + 48#64)
    (atCounter : t.locals.lookup (ofString "i") = some (ValueHOL.val (HolWordLab.word I0)))
    (atNwd : t.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)))
    (atPl : t.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : t.locals.lookup (ofString "e") = none)
    (atSlices : t.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)))
    (atHeap : t.globals.lookup (ofString "heap_ptr") = some (ValueHOL.val (HolWordLab.word heapBase)))
    (code : t.code = originalRuntimeCode)
    (heap0 : H 0 = heapBase)
    (heapStep : ∀ j, H (j + 1) = allocationEnd (H j) 64)
    (initialLe : I0.toNat ≤ nwd.toNat)
    (smallNwd : nwd.toNat < 2^63)
    (bounds : ∀ j, j ≤ nwd.toNat → (H j).toNat + 64 < 2^64)
    (outW : ∀ j, j ≤ nwd.toNat → ¬ MWin (H j) 64 w)
    (outR : ∀ j, j ≤ nwd.toNat → ¬ MWin (H j) 64 read)
    (addrRead : t.memaddrs read)
    (sliceW : ∀ j, j ≤ nwd.toNat →
      w ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 ∧
      w ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 + 8#64)
    (sliceR : ∀ j, j ≤ nwd.toNat →
      read ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 ∧
      read ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 + 8#64)
    (memRead : t.memory read = HolWordLab.word X)
    (tail : (evaluateHOLFiniteState (evaluateHOLFiniteState t wdSliceLoop).2
        (actualPayloadHeaderAt 47)).2.memory w = (evaluateHOLFiniteState t wdSliceLoop).2.memory w) :
    (evaluateHOLFiniteState t (actualPayloadHeaderAt 46)).2.memory w = t.memory w := by
  have loopWin : (evaluateHOLFiniteState t wdSliceLoop).2.memory w = t.memory w :=
    wdSliceLoop_window t I0 nwd pl slices heapBase w read X H readEq atCounter atNwd atPl freshE
      atSlices atHeap code heap0 heapStep initialLe smallNwd bounds outW outR addrRead sliceW sliceR
      memRead
  rw [source_wd_slice_loop,evaluateHOLFiniteState_seq_line780]
  cases hloop : evaluateHOLFiniteState t wdSliceLoop with
  | mk r s' =>
    rw [hloop] at tail loopWin
    dsimp only
    split
    · rw [tail]
      exact loopWin
    · simpa using loopWin

#print axioms payloadHeader46_window
end InitECandidate.Runtime
