import InitECandidate.Runtime.HashNewPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Header allocation and scalar stores reach the next actual allocation with
its argument locals and heap frontier available, independent of later space. -/
theorem evaluate_htabNew_prefix_initialized {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (request : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer 72).toNat ≤ 33806089496)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain0 : state.memaddrs (pointer + 0)) (domain8 : state.memaddrs (pointer + 8))
    (domain16 : state.memaddrs (pointer + 16)) (domain24 : state.memaddrs (pointer + 24)) :
    ∃ ready, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new) =
      (let output := evaluateHOLFiniteState ready htabNewAfterHeader;
        (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq output.2.locals (ofString "stride",state.locals.lookup (ofString "stride")))
          (ofString "t",state.locals.lookup (ofString "t")))})) ∧
      ready.clock = state.clock - 1 ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 72))) ∧
      ready.locals.lookup (ofString "t") = some (.val (.word pointer)) ∧
      ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
      ready.locals.lookup (ofString "stride") = some (.val (.word (allocationEnd 0 keyLength))) := by
  obtain ⟨allocated,_,ticks,_,locals,postCode,domain,_,_,globals,declaration⟩ :=
    evaluate_alloc_call_and_declaration state (.const 72) pointer 72 rfl code clock heap request finish
  let bound := setVarHOLFinite (ofString "t") (.val (.word pointer)) allocated
  let entered := setVarHOLFinite (ofString "stride") (.val (.word (allocationEnd 0 keyLength))) bound
  let ready := htabNewHeaderPost entered pointer keyLength (allocationEnd 0 keyLength) capacity
  have t : bound.locals.lookup (ofString "t") = some (.val (.word pointer)) := by
    simp [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have k : bound.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    simpa [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,show ofString "t" ≠ ofString "key_len" from by decide] using keyLocal
  have c : bound.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,show ofString "t" ≠ ofString "cap" from by decide] using capLocal
  have strideOld : bound.locals.lookup (ofString "stride") = state.locals.lookup (ofString "stride") := by
    simp [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,show ofString "t" ≠ ofString "stride" from by decide]
  have headerRun := evaluate_htabNew_stride_header bound pointer keyLength capacity htabNewAfterHeader t k c
    (by simpa only [bound,setVarHOLFinite,domain] using domain0)
    (by simpa only [bound,setVarHOLFinite,domain] using domain8)
    (by simpa only [bound,setVarHOLFinite,domain] using domain16)
    (by simpa only [bound,setVarHOLFinite,domain] using domain24)
  refine ⟨ready,?_,ticks,postCode,domain,?_,?_,?_,?_⟩
  · rw [source_htabNew_header,declaration]
    change (let output := evaluateHOLFiniteState bound (.dec (ofString "stride") .one htabNewStrideExpression (htabNewHeader htabNewAfterHeader)); _) = _
    rw [headerRun]
    simp only [strideOld]
    rfl
  · change allocated.globals.lookup _ = _
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa [ready,htabNewHeaderPost,sourceWriteWord,entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "stride" ≠ ofString "t" from by decide] using t
  · simpa [ready,htabNewHeaderPost,sourceWriteWord,entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "stride" ≠ ofString "cap" from by decide] using c
  · simp [ready,htabNewHeaderPost,sourceWriteWord,entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms evaluate_htabNew_prefix_initialized
end InitECandidate.Runtime
