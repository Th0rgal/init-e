import InitECandidate.Runtime.HashNewPrefixInitialized
import InitECandidate.Runtime.HashNewKeysAllocation
import InitECandidate.Runtime.HashNewArrayFailures
import InitECandidate.Runtime.HashNewValuesAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful header, keys and values allocation followed by used-array
rejection produce an actual constructor-body exit in five source clocks. -/
theorem evaluate_htabNew_body_used_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer keyLength capacity : BitVec 64) (code : state.code = originalRuntimeCode) (ticks : 5 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (headerRequest : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (headerFinish : (allocationEnd pointer 72).toNat ≤ 33806089496)
    (keysRequest : capacity * allocationEnd 0 keyLength ≤ (33806089496 : BitVec 64) - allocationEnd pointer 72)
    (keysFinish : (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)).toNat ≤ 33806089496)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domains : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (valuesRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength))
    (valuesFinish : (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)).toNat ≤ 33806089496)
    (usedRejected : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)).toNat < capacity.toNat) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 ≠ none ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 ≠ some .timeOut ∧
      (∀ value, (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 ≠ some (.returned value)) ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).2.clock = state.clock - 5 := by
  obtain ⟨header,headerRun,headerClock,headerCode,headerDomain,headerHeap,tLocal,cLocal,strideLocal⟩ :=
    evaluate_htabNew_prefix_initialized state pointer keyLength capacity code (by omega) heap headerRequest headerFinish keyLocal capLocal
      (domains 0 (by simp)) (domains 8 (by simp)) (domains 16 (by simp)) (domains 24 (by simp))
  have args : evalListHOLFinite header (h := fun address => Classical.propDecidable (header.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.var .local (ofString "stride")]] = some [.val (.word (capacity * allocationEnd 0 keyLength))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,cLocal,strideLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨values,keysRun,keysClock,keysLocals,_,_,keysHeap,keysCode,keysDomain,_⟩ :=
    evaluate_allocation_pointer_store header (ofString "keys") (ofString "t") _ (allocationEnd pointer 72)
      (capacity * allocationEnd 0 keyLength) pointer 32 htabNewValuesAllocation (by decide) args (headerCode.trans code)
      (by omega) headerHeap keysRequest keysFinish tLocal (by rw [headerDomain]; exact domains 32 (by simp))
  have capAfter : values.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [keysLocals]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "keys" ≠ ofString "cap" from by decide] using cLocal
  have tableAfter : values.locals.lookup (ofString "t") = some (.val (.word pointer)) := by
    rw [keysLocals]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "keys" ≠ ofString "t" from by decide] using tLocal
  have valueArgs : evalListHOLFinite values (h := fun address => Classical.propDecidable (values.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capAfter,panOpHOL,valueIsWord,valueWord]
  obtain ⟨used,valuesRun,valuesClock,valuesLocals,_,_,valuesHeap,valuesCode,valuesDomain,_⟩ :=
    evaluate_allocation_pointer_store values (ofString "vals") (ofString "t") _
      (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength))
      (capacity * 8) pointer 40 htabNewUsedAllocation (by decide) valueArgs (keysCode.trans (headerCode.trans code))
      (by omega) keysHeap valuesRequest valuesFinish tableAfter (by rw [keysDomain,headerDomain]; exact domains 40 (by simp))
  have capUsed : used.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [valuesLocals]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "vals" ≠ ofString "cap" from by decide] using capAfter
  have failure := evaluate_htabNew_used_allocation_failure used _ capacity (valuesCode.trans (keysCode.trans (headerCode.trans code))) valuesHeap capUsed usedRejected (by omega)
  have actualValuesRun : evaluateHOLFiniteState values htabNewValuesAllocation =
      (let output := evaluateHOLFiniteState used htabNewUsedAllocation;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "vals",values.locals.lookup (ofString "vals"))})) := by
    rw [source_htabNew_values_allocation]
    exact valuesRun
  have actualKeysRun : evaluateHOLFiniteState header htabNewAfterHeader =
      (let output := evaluateHOLFiniteState values htabNewValuesAllocation;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "keys",header.locals.lookup (ofString "keys"))})) := by
    rw [source_htabNew_keys_allocation]
    exact keysRun
  have firstResult := congrArg Prod.fst headerRun
  change (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 = (evaluateHOLFiniteState header htabNewAfterHeader).1 at firstResult
  have secondResult := congrArg Prod.fst actualKeysRun
  change (evaluateHOLFiniteState header htabNewAfterHeader).1 = (evaluateHOLFiniteState values htabNewValuesAllocation).1 at secondResult
  have firstClock := congrArg (fun output => output.2.clock) headerRun
  change (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).2.clock = (evaluateHOLFiniteState header htabNewAfterHeader).2.clock at firstClock
  have secondClock := congrArg (fun output => output.2.clock) actualKeysRun
  change (evaluateHOLFiniteState header htabNewAfterHeader).2.clock = (evaluateHOLFiniteState values htabNewValuesAllocation).2.clock at secondClock
  have thirdResult := congrArg Prod.fst actualValuesRun
  change (evaluateHOLFiniteState values htabNewValuesAllocation).1 = (evaluateHOLFiniteState used htabNewUsedAllocation).1 at thirdResult
  have thirdClock := congrArg (fun output => output.2.clock) actualValuesRun
  change (evaluateHOLFiniteState values htabNewValuesAllocation).2.clock = (evaluateHOLFiniteState used htabNewUsedAllocation).2.clock at thirdClock
  refine ⟨by rw [firstResult,secondResult,thirdResult]; exact failure.1,by rw [firstResult,secondResult,thirdResult]; exact failure.2.1,?_,?_⟩
  · intro value
    rw [firstResult,secondResult,thirdResult]; exact failure.2.2.1 value
  · rw [firstClock,secondClock,thirdClock,failure.2.2.2,valuesClock,keysClock,headerClock]
    omega

#print axioms evaluate_htabNew_body_used_failure
end InitECandidate.Runtime
