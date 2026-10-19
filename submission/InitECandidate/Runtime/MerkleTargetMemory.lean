import InitECandidate.Runtime.MerkleAfterTargetMemory
import InitECandidate.Runtime.MerkleTargetBound
import InitECandidate.Runtime.MaximumReturnedRange
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleTarget_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial dl out n input watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word buf)))
    (heapBound : buf.toNat ≤ 33806089496)
    (atIndex : state.locals.lookup (ofString "dn") = some (.val (.word initial)))
    (atDl : state.locals.lookup (ofString "dl") = some (.val (.word dl)))
    (dlBound : dl.toNat ≤ 63)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengths : MerkleChunkLengths n ((1#64) <<< initial.toNat))
    (depthBound : initial.toNat ≤ 27)
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (aligned : buf.toNat % 8 = 0)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : 1 + (16 + (1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16)))))) ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 2) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "max") =
      some ([(ofString "a",.one),(ofString "b",.one)],sourceFunctionBody Guest.guestFn_max,.one) := by
    rw [code]; exact vmLookup_max
  have lookup := pan_two_word_lookup state.code.lookup (ofString "max") (ofString "a") (ofString "b")
    (sourceFunctionBody Guest.guestFn_max) dl initial (by decide) installed
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "dl"),.var .local (ofString "dn")] = some [.val (.word dl),.val (.word initial)] := by
    simp [evalListHOLExact,evalHOLExact,atDl,atIndex]
  rw [source_merkleTarget] at run
  obtain ⟨returned,bodyPost,ready,output,bodyRun,rlocals,rmem,rglobals,rclock,_,_,rcode,tail,scope⟩ :=
    evaluate_decCall_returned_global_memory_clock_scope state post (ofString "target") (ofString "max")
      .one .one _ _ _ (merkleizeAt 3) _ value args lookup run
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "a",.val (.word dl))).update (ofString "b",.val (.word initial)))
  have left : entry.locals.lookup (ofString "a") = some (.val (.word dl)) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have right : entry.locals.lookup (ofString "b") = some (.val (.word initial)) := by
    simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨target,rfl,_,above,bounded,bodyPostEq⟩ := max_body_returned_range entry bodyPost dl initial returned 63
    left right dlBound (depthBound.trans (by decide)) bodyRun
  have readyMemory : ready.memory = state.memory := by rw [rmem,bodyPostEq]; rfl
  have readyGlobals : ready.globals = state.globals := by rw [rglobals,bodyPostEq]; rfl
  have readyCode : ready.code = state.code := by rw [rcode,bodyPostEq]; rfl
  have readyClock : ready.clock = state.clock - 1 := by rw [rclock,bodyPostEq]; rfl
  let next := setVarHOLFinite (ofString "target") (.val (.word target)) ready
  have keep (key : MlS) (different : key ≠ ofString "target") : next.locals.lookup key = state.locals.lookup key := by
    simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,rlocals]
  have enough : 16 + (1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16))))) ≤ next.clock := by
    change _ ≤ ready.clock
    rw [readyClock]
    apply Nat.le_sub_of_add_le
    simpa only [Nat.add_comm] using budget
  have frame := merkleAfterTarget_returned_memory next output pointer accelerator buf zeroHashes initial target out n input watched value
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact atPointer)
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact atAccel)
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact atZero)
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact heap) heapBound
    ((keep _ (by decide)).trans atIndex)
    (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((keep _ (by decide)).trans atN) ((keep _ (by decide)).trans atInput) lengths depthBound
    ((keep _ (by decide)).trans atOut) outAligned outFits outOutside above bounded aligned before accelAligned accelFits pointerFits
    accelOutside pointerOutside (by exact readyCode.trans code) enough tail
  rw [scope]
  exact frame.trans (congrFun readyMemory watched)

#print axioms merkleTarget_suffix_returned_memory
end InitECandidate.Runtime
