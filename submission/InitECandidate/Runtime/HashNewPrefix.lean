import InitECandidate.Runtime.HashNewHeader
import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The stride declaration and four header stores execute without spending
source clocks, then restore the declaration's previous local on exit. -/
theorem evaluate_htabNew_stride_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64) (continuation : ProgHOL 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain0 : state.memaddrs (table + 0)) (domain8 : state.memaddrs (table + 8))
    (domain16 : state.memaddrs (table + 16)) (domain24 : state.memaddrs (table + 24)) :
    evaluateHOLFiniteState state (.dec (ofString "stride") .one htabNewStrideExpression
      (htabNewHeader continuation)) =
      (let entered := setVarHOLFinite (ofString "stride") (.val (.word (allocationEnd 0 keyLength))) state;
       let output := evaluateHOLFiniteState
         (htabNewHeaderPost entered table keyLength (allocationEnd 0 keyLength) capacity) continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "stride",state.locals.lookup (ofString "stride")))})) := by
  let entered := setVarHOLFinite (ofString "stride") (.val (.word (allocationEnd 0 keyLength))) state
  have nt : ofString "stride" ≠ ofString "t" := by decide
  have nk : ofString "stride" ≠ ofString "key_len" := by decide
  have nc : ofString "stride" ≠ ofString "cap" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt,nk,nc] using tableLocal
  have k : entered.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt,nk,nc] using keyLocal
  have c : entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt,nk,nc] using capLocal
  have stride : entered.locals.lookup (ofString "stride") = some (.val (.word (allocationEnd 0 keyLength))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have run := evaluate_htabNew_header entered table keyLength (allocationEnd 0 keyLength) capacity
    continuation t k stride c domain0 domain8 domain16 domain24
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_htabNew_stride state keyLength keyLocal]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (allocationEnd 0 keyLength)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk,run]

/-- The original constructor reaches its array-allocation continuation after
one allocator clock, with the scalar header initialized. Both declaration
scopes are restored when that continuation exits. -/
theorem evaluate_htabNew_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (request : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 72).toNat ≤ 33806089496)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain0 : state.memaddrs (pointer + 0)) (domain8 : state.memaddrs (pointer + 8))
    (domain16 : state.memaddrs (pointer + 16)) (domain24 : state.memaddrs (pointer + 24)) :
    ∃ ready, ready.clock = state.clock - 1 ∧ ready.locals = state.locals ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new) =
        (let bound := setVarHOLFinite (ofString "t") (.val (.word pointer)) ready;
         let entered := setVarHOLFinite (ofString "stride") (.val (.word (allocationEnd 0 keyLength))) bound;
         let output := evaluateHOLFiniteState
           (htabNewHeaderPost entered pointer keyLength (allocationEnd 0 keyLength) capacity) htabNewAfterHeader;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq
           (HolFiniteMapExact.resVarEq output.2.locals (ofString "stride",bound.locals.lookup (ofString "stride")))
           (ofString "t",state.locals.lookup (ofString "t")))})) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 72] =
        some [.val (.word (72 : BitVec 64))] := by rfl
  obtain ⟨ready,_,ticks,_,locals,_,domain,_,_,_,decl⟩ :=
    evaluate_alloc_call_and_declaration state (.const 72) pointer 72 arguments code clock heapGlobal request finishBound
  let bound := setVarHOLFinite (ofString "t") (.val (.word pointer)) ready
  have nt : ofString "t" ≠ ofString "key_len" := by decide
  have nc : ofString "t" ≠ ofString "cap" := by decide
  have t : bound.locals.lookup (ofString "t") = some (.val (.word pointer)) := by
    simp [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have k : bound.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    simpa [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt,locals] using keyLocal
  have c : bound.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc,locals] using capLocal
  have run := evaluate_htabNew_stride_header bound pointer keyLength capacity htabNewAfterHeader t k c
    (by simpa [bound,setVarHOLFinite,domain] using domain0)
    (by simpa [bound,setVarHOLFinite,domain] using domain8)
    (by simpa [bound,setVarHOLFinite,domain] using domain16)
    (by simpa [bound,setVarHOLFinite,domain] using domain24)
  refine ⟨ready,ticks,locals,?_⟩
  rw [source_htabNew_header,decl]
  change (let output := evaluateHOLFiniteState bound (.dec (ofString "stride") .one htabNewStrideExpression (htabNewHeader htabNewAfterHeader)); _) = _
  rw [run]

#print axioms evaluate_htabNew_prefix
#print axioms evaluate_htabNew_stride_header
end InitECandidate.Runtime
