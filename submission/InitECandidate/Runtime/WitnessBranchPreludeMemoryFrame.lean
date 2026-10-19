import InitECandidate.Runtime.WitnessBranchIncrementMemoryFrame
import InitECandidate.Runtime.WitnessBranchPreludeClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_branch_prelude_normal_memory_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (indexBound : index.toNat<16) (heapBound : heap.toNat ≤ 33806089496)
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
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    post.globals.lookup (ofString "heap_ptr")=s.globals.lookup (ofString "heap_ptr") ∧
    ∀ watched : BitVec 64, ceiling≤watched.toNat → watched.toNat<heap.toNat →
      watched≠top+32 → watched≠top+40 → post.memory watched=s.memory watched := by
  obtain ⟨ready,locals,globals,codeEq,domain,endian,clock,tailRun,memory⟩ :=
    witness_branch_prelude_clocked_normal_continuation s post top heap index result
      atTop atBr atIndex atResult code run
  have addNat (base : BitVec 64) (offset : Nat) (small : base.toNat+offset < 2^64) :
      (base+BitVec.ofNat 64 offset).toNat=base.toNat+offset := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : offset<2^64),Nat.mod_eq_of_lt small]
  have product : (index*8).toNat=index.toNat*8 := by
    rw [BitVec.toNat_mul]
    change index.toNat*8%2^64=index.toNat*8
    omega
  have childNat : (heap+32+index*8).toNat=heap.toNat+32+index.toNat*8 := by
    rw [BitVec.toNat_add,product]
    have heap32 : (heap+32).toNat=heap.toNat+32 := addNat heap 32 (by omega)
    rw [heap32]
    exact Nat.mod_eq_of_lt (by omega)
  have top40Nat : (top+40#64).toNat=top.toNat+40 := addNat top 40 (by omega)
  have top24Nat : (top+24#64).toNat=top.toNat+24 := addNat top 24 (by omega)
  have pointerNat : (array+(16#64)*16#64).toNat=array.toNat+256 := by
    have factor : (16#64)*16#64=256#64 := by decide
    rw [factor];exact addNat array 256 (by omega)
  have lengthNat : (array+(16#64)*16#64+8#64).toNat=array.toNat+264 := by
    have factor : (16#64)*16#64=256#64 := by decide
    rw [factor,BitVec.add_assoc];exact addNat array 264 (by omega)
  have kept (watched : BitVec 64) (below : watched.toNat<heap.toNat) (notOcc : watched≠top+40) :
      ready.memory watched=s.memory watched := by
    apply memory watched
    · intro same
      have equal := congrArg BitVec.toNat same
      rw [childNat] at equal
      omega
    · exact notOcc
  have arrayKept := kept (top+24#64) (by rw [top24Nat];omega) (by
    intro same;have equal:=congrArg BitVec.toNat same;change (top+24#64).toNat=(top+40#64).toNat at equal;rw [top24Nat,top40Nat] at equal;omega)
  have ptrKept := kept (array+(16#64)*16#64) (by rw [pointerNat];omega) (by
    intro same;have equal:=congrArg BitVec.toNat same;change (array+(16#64)*16#64).toNat=(top+40#64).toNat at equal;rw [pointerNat,top40Nat] at equal;omega)
  have lenKept := kept (array+(16#64)*16#64+8#64) (by rw [lengthNat];omega) (by
    intro same;have equal:=congrArg BitVec.toNat same;change (array+(16#64)*16#64+8#64).toNat=(top+40#64).toNat at equal;rw [lengthNat,top40Nat] at equal;omega)
  obtain ⟨scratchPost,framePost,heapPost,tailMemory⟩ := witness_branch_increment_normal_memory_frame ready post
    array pointer length scratch frame top heap index ceiling inputLimit
    (by rw [domain];exact arrayReadable) (arrayKept.trans arrayCell)
    (by rw [locals];exact atTop) (by rw [locals];exact atBr) (by rw [locals];exact atIndex) heapBound
    (slice.after_frame s ready array 16 pointer length domain ptrKept lenKept)
    inputRange lengthBound limitBound (by rw [globals];exact scratchGlobal) (by rw [globals];exact frameGlobal)
    (codeEq.trans code) orderedFrame framePositive scratchBelow
    (by intro address lower upper;rw [domain];exact arena address lower upper) (by rw [clock];exact budget) tailRun
  exact ⟨scratchPost,framePost,heapPost.trans (by rw [globals]),
    fun watched above below notIndex notOcc => (tailMemory watched above below notIndex).trans (kept watched below notOcc)⟩

#print axioms witness_branch_prelude_normal_memory_frame
end InitECandidate.Runtime
