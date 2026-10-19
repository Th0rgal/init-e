import InitECandidate.Runtime.MerkleTargetMemory
import InitECandidate.Runtime.MerkleizeBodyBound
import InitECandidate.Runtime.ReturnedCallClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleCountDepth_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes dl out n input watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word buf)))
    (heapBound : buf.toNat ≤ 33806089496)
    (atDl : state.locals.lookup (ofString "dl") = some (.val (.word dl)))
    (dlBound : dl.toNat ≤ 63)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (inputBound : n.toNat ≤ 134217712)
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (aligned : buf.toNat % 8 = 0)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : 65 + (1 + (16 + (1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16))))))) ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 1) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "ceil_log2") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_ceil_log2,.one) := by
    rw [code]; exact originalRuntimeCode_ceilLog2_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "ceil_log2") (ofString "n")
    (sourceFunctionBody Guest.guestFn_ceil_log2) n installed
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "n")] = some [.val (.word n)] := by simp [evalListHOLExact,evalHOLExact,atN]
  rw [source_merkleCountDepth] at run
  obtain ⟨returned,bodyPost,ready,output,bodyRun,rlocals,rmem,rglobals,rclock,_,_,rcode,tail,scope⟩ :=
    evaluate_decCall_returned_global_memory_clock_scope state post (ofString "dn") (ofString "ceil_log2")
      .one .one _ _ _ (merkleizeAt 2) _ value args lookup run
  let entry := callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "n",.val (.word n)))
  have argument : entry.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨dn,rfl,depthBound,lengths⟩ := merkleChunkLengths_of_ceilLog2_returned entry bodyPost n returned argument inputBound bodyRun
  have memory := evaluate_readOnly_memory _ ceilLog2_readOnly entry
  have globals := evaluate_readOnly_globals _ ceilLog2_readOnly entry
  have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ceil_log2)
  have bodyBudget : 64 ≤ entry.clock := by
    change 64 ≤ state.clock - 1
    exact Nat.le_sub_of_add_le ((Nat.le_add_right 65 _).trans budget)
  have spent := (ceilLog2_body_bounded entry (by exact code) bodyBudget).1
  rw [bodyRun] at memory globals meta' spent
  have readyMemory : ready.memory = state.memory := rmem.trans memory
  have readyGlobals : ready.globals = state.globals := rglobals.trans globals
  have readyCode : ready.code = state.code := rcode.trans meta'.1
  let next := setVarHOLFinite (ofString "dn") (.val (.word dn)) ready
  have keep (key : MlS) (different : key ≠ ofString "dn") : next.locals.lookup key = state.locals.lookup key := by
    simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,rlocals]
  have enough : 1 + (16 + (1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16)))))) ≤ next.clock := by
    change _ ≤ ready.clock
    rw [rclock]
    exact returned_call_tail_clock state.clock bodyPost.clock 64 _ budget spent
  have frame := merkleTarget_suffix_returned_memory next output pointer accelerator buf zeroHashes dn dl out n input watched value
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact atPointer)
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact atAccel)
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact atZero)
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact heap) heapBound
    (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((keep _ (by decide)).trans atDl) dlBound ((keep _ (by decide)).trans atN) ((keep _ (by decide)).trans atInput)
    lengths depthBound ((keep _ (by decide)).trans atOut) outAligned outFits outOutside aligned before accelAligned accelFits pointerFits
    accelOutside pointerOutside (by exact readyCode.trans code) enough tail
  rw [scope]
  exact frame.trans (congrFun readyMemory watched)

#print axioms merkleCountDepth_suffix_returned_memory
end InitECandidate.Runtime
