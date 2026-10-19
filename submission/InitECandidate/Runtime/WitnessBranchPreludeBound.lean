import InitECandidate.Runtime.WitnessBranchIncrementBound
import InitECandidate.Runtime.WitnessBranchPreludeReach
import InitECandidate.Runtime.WitnessBranchPreludeClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString


theorem runBounded_witness_branch_prelude {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (indexBound : index.toNat < 16)
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    : RunBounded s (witnessBranchAt 2) (witnessBranchFinishCost length.toNat) := by
  have reached := witness_branch_prelude_reaches s top heap index result atTop atBr atIndex atResult code
  have bounded := RunBounded.ofReaches (tailCost := witnessBranchFinishCost length.toNat)
    (by simpa using budget) reached (by
      intro ready facts ticks
      obtain ⟨locals,globals,codeEq,domain,endian,memory⟩ := facts
      have addNat (base : BitVec 64) (offset : Nat) (small : base.toNat+offset < 2^64) :
          (base+BitVec.ofNat 64 offset).toNat = base.toNat+offset := by
        rw [BitVec.toNat_add,BitVec.toNat_ofNat]
        have off : offset < 2^64 := by omega
        rw [Nat.mod_eq_of_lt off,Nat.mod_eq_of_lt small]
      have productNat : (index*(8 : BitVec 64)).toNat=index.toNat*8 := by
        rw [BitVec.toNat_mul]
        change (index.toNat*8)%2^64=index.toNat*8
        exact Nat.mod_eq_of_lt (by omega)
      have firstNat : (heap+(32 : BitVec 64)).toNat=heap.toNat+32 := by
        rw [BitVec.toNat_add]
        change (heap.toNat+32)%2^64=heap.toNat+32
        exact Nat.mod_eq_of_lt (by omega)
      have childNat : (heap+(32 : BitVec 64)+index*(8 : BitVec 64)).toNat=heap.toNat+32+index.toNat*8 := by
        rw [BitVec.toNat_add,firstNat,productNat]
        exact Nat.mod_eq_of_lt (by omega)
      have top40Nat : (top+40#64).toNat = top.toNat+40 := addNat top 40 (by omega)
      have top24Nat : (top+24#64).toNat = top.toNat+24 := addNat top 24 (by omega)
      have pointerNat : (array+(16#64)*16#64).toNat = array.toNat+256 := by
        have product : (16#64)*16#64=256#64 := by decide
        rw [product]
        exact addNat array 256 (by omega)
      have lengthNat : (array+(16#64)*16#64+8#64).toNat = array.toNat+264 := by
        have product : (16#64)*16#64=256#64 := by decide
        rw [product,BitVec.add_assoc]
        exact addNat array 264 (by omega)
      have kept (watched : BitVec 64) (below : watched.toNat < heap.toNat)
          (notOcc : watched.toNat ≠ top.toNat+40) : ready.memory watched=s.memory watched := by
        apply memory watched
        · intro same
          have equal := congrArg BitVec.toNat same
          rw [childNat] at equal
          omega
        · intro same
          have equal := congrArg BitVec.toNat same
          change watched.toNat = (top+40#64).toNat at equal
          rw [top40Nat] at equal
          exact notOcc equal
      have arrayFrame := kept (top+24#64) (by rw [top24Nat]; omega) (by rw [top24Nat]; omega)
      have ptrFrame := kept (array+(16#64)*16#64) (by rw [pointerNat]; omega) (by rw [pointerNat]; omega)
      have lenFrame := kept (array+(16#64)*16#64+8#64) (by rw [lengthNat]; omega) (by rw [lengthNat]; omega)
      exact runBounded_witness_branch_increment ready array pointer length scratch frame top ceiling inputLimit
        (by rw [locals]; exact atTop) (by rw [domain]; exact arrayReadable) (arrayFrame.trans arrayCell)
        (slice.after_frame s ready array 16 pointer length domain ptrFrame lenFrame)
        inputRange lengthBound limitBound (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
        (codeEq.trans code) orderedFrame framePositive scratchBelow
        (by intro address lower upper; rw [domain]; exact arena address lower upper) ticks)
  simpa using bounded

#print axioms runBounded_witness_branch_prelude
end InitECandidate.Runtime
