import InitECandidate.Runtime.MerkleCountDepthMemory
import InitECandidate.Runtime.MerkleizeCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleize_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes limitWord out n input watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word buf)))
    (heapBound : buf.toNat ≤ 33806089496)
    (atLimit : state.locals.lookup (ofString "limit") = some (.val (.word limitWord)))
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
    (budget : 65 + (65 + (1 + (16 + (1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16)))))))) ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_merkleize) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "ceil_log2") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_ceil_log2,.one) := by
    rw [code]; exact originalRuntimeCode_ceilLog2_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "ceil_log2") (ofString "n")
    (sourceFunctionBody Guest.guestFn_ceil_log2) limitWord installed
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "limit")] = some [.val (.word limitWord)] := by simp [evalListHOLExact,evalHOLExact,atLimit]
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (merkleizeAt 0) = _ at run
  rw [source_merkleLimitDepth] at run
  obtain ⟨returned,bodyPost,ready,output,bodyRun,rlocals,rmem,rglobals,rclock,_,_,rcode,tail,scope⟩ :=
    evaluate_decCall_returned_global_memory_clock_scope state post (ofString "dl") (ofString "ceil_log2")
      .one .one _ _ _ (merkleizeAt 1) _ value args lookup run
  let entry := callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "n",.val (.word limitWord)))
  have argument : entry.locals.lookup (ofString "n") = some (.val (.word limitWord)) := by
    simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨dl,dlSmall,rfl,_⟩ := ceilLog2_body_returned entry bodyPost limitWord returned argument bodyRun
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
  let next := setVarHOLFinite (ofString "dl") (.val (.word dl)) ready
  have keep (key : MlS) (different : key ≠ ofString "dl") : next.locals.lookup key = state.locals.lookup key := by
    simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,rlocals]
  have enough : 65 + (1 + (16 + (1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16))))))) ≤ next.clock := by
    change _ ≤ ready.clock
    rw [rclock]
    exact returned_call_tail_clock state.clock bodyPost.clock 64 _ budget spent
  have frame := merkleCountDepth_suffix_returned_memory next output pointer accelerator buf zeroHashes dl out n input watched value
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact atPointer)
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact atAccel)
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact atZero)
    (by change ready.globals.lookup _ = _; rw [readyGlobals]; exact heap) heapBound
    (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (Nat.le_of_lt_succ dlSmall) ((keep _ (by decide)).trans atN) ((keep _ (by decide)).trans atInput)
    inputBound ((keep _ (by decide)).trans atOut) outAligned outFits outOutside aligned before accelAligned accelFits pointerFits
    accelOutside pointerOutside (by exact readyCode.trans code) enough tail
  rw [scope]
  exact frame.trans (congrFun readyMemory watched)

theorem merkleize_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer accelerator buf zeroHashes limitWord out n input watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word input),.val (.word n),.val (.word limitWord),.val (.word out)])
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word buf)))
    (heapBound : buf.toNat ≤ 33806089496)
    (inputBound : n.toNat ≤ 134217712)
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (aligned : buf.toNat % 8 = 0)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : merkleBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "merkleize") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "merkleize") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "limit",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_merkleize,.one) := by
    rw [code]; exact originalRuntimeCode_merkleize_lookup
  have lookup := pan_four_word_lookup state.code.lookup (ofString "merkleize")
    (ofString "p") (ofString "n") (ofString "limit") (ofString "out")
    (sourceFunctionBody Guest.guestFn_merkleize) input n limitWord out
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  obtain ⟨returned,output,bodyRun,_,scope⟩ := evaluate_discardCall_normal_result state post (ofString "merkleize")
    .one arguments _ _ _ args lookup run
  let entry := callEntryStateHOLFinite state
    ((((HolFiniteMapExact.empty.update (ofString "p",.val (.word input))).update (ofString "n",.val (.word n))).update
      (ofString "limit",.val (.word limitWord))).update (ofString "out",.val (.word out)))
  have frameBudget : 65 + (65 + (1 + (16 + (1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost +
      (merkleInputTreeCost + merklePaddingCost + 16)))))))) ≤ entry.clock := by
    change _ ≤ state.clock - 1
    apply Nat.le_sub_of_add_le
    exact (show (65 + (65 + (1 + (16 + (1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost +
      (merkleInputTreeCost + merklePaddingCost + 16))))))))) + 1 ≤ merkleBodyCost + 1 by decide).trans budget
  rw [scope]
  exact merkleize_body_returned_memory entry output pointer accelerator buf zeroHashes limitWord out n input watched returned
    atPointer atAccel atZero heap heapBound
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    inputBound (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    outAligned outFits outOutside aligned before accelAligned accelFits pointerFits accelOutside pointerOutside code frameBudget bodyRun

#print axioms merkleize_body_returned_memory
#print axioms merkleize_call_normal_memory
end InitECandidate.Runtime
