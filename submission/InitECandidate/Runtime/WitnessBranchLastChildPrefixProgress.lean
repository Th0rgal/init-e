import InitECandidate.Runtime.WitnessBranchLastChildProgress
import InitECandidate.Runtime.WitnessBranchPreludeClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Concrete record/table/branch geometry carries the original final-child
store and occupancy update into the complete final parser and parent pop. -/
theorem witness_branch_last_child_prefix_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap prev : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word (15#64))))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (prevCell : s.memory top = .word prev) (topAbove : ceiling ≤ top.toNat)
    (before : top.toNat < heap.toNat) (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    (run : evaluateHOLFiniteState s (witnessBranchAt 2) = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word prev)) ∧
      post.locals.lookup (ofString "result") = some (.val (.word heap)) ∧
      post.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") ∧
      post.memory top = s.memory top := by
  obtain ⟨ready,locals,globals,codeEq,domain,endian,clock,tailRun,memory⟩ :=
    witness_branch_prelude_clocked_normal_continuation s post top heap (15#64) result
      atTop atBr atIndex atResult code run
  have addNat (base : BitVec 64) (offset : Nat) (small : base.toNat+offset < 2^64) :
      (base+BitVec.ofNat 64 offset).toNat = base.toNat+offset := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    have off : offset < 2^64 := by omega
    rw [Nat.mod_eq_of_lt off,Nat.mod_eq_of_lt small]
  have childNat : (heap+32+(15#64)*8).toNat = heap.toNat+152 := by
    have product : (15#64)*8 = 120#64 := by decide
    rw [product,BitVec.add_assoc]
    exact addNat heap 152 (by omega)
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
  have prevFrame := kept top before (by omega)
  have arrayFrame := kept (top+24#64) (by rw [top24Nat]; omega) (by rw [top24Nat]; omega)
  have ptrFrame := kept (array+(16#64)*16#64) (by rw [pointerNat]; omega) (by rw [pointerNat]; omega)
  have lenFrame := kept (array+(16#64)*16#64+8#64) (by rw [lengthNat]; omega) (by rw [lengthNat]; omega)
  obtain ⟨topPost,resultPost,modePost,cellPost⟩ := witness_branch_last_child_normal_progress ready post
    array pointer length scratch frame top heap prev ceiling inputLimit
    (by rw [domain]; exact arrayReadable) (arrayFrame.trans arrayCell)
    (by rw [locals]; exact atTop) (by rw [locals]; exact atIndex) (by rw [locals]; exact atBr)
    (prevFrame.trans prevCell) topAbove before heapBound
    (slice.after_frame s ready array 16 pointer length domain ptrFrame lenFrame)
    inputRange lengthBound limitBound (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
    (codeEq.trans code) orderedFrame framePositive scratchBelow
    (by intro address lower upper; rw [domain]; exact arena address lower upper)
    (by rw [clock]; exact budget) tailRun
  exact ⟨topPost,resultPost,modePost.trans (by rw [locals]),cellPost.trans prevFrame⟩

#print axioms witness_branch_last_child_prefix_normal_progress
end InitECandidate.Runtime
