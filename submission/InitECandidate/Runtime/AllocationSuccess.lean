import InitECandidate.Runtime.AllocationSource
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete successful execution of the original alloc body, at any source
clock. Both scope restorations and both guard decisions use the real evaluator. -/
theorem evaluate_source_alloc_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size : BitVec 64)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer size).toNat ≤ 33806089496) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_alloc) =
        (some (.returned (.val (.word pointer))),post) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.eshapes = state.eshapes ∧
      post.be = state.be ∧ post.globals = (setGlobalHOLFinite (ofString "heap_ptr")
        (.val (.word (allocationEnd pointer size))) state).globals := by
  classical
  let pState := setVarHOLFinite (ofString "p") (.val (.word pointer)) state
  let qState := setVarHOLFinite (ofString "q") (.val (.word (allocationEnd pointer size))) pState
  let returned := emptyLocalsHOLFinite
    (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word (allocationEnd pointer size))) qState)
  let qPost := {returned with locals := (HolFiniteMapExact.resVarEq returned.locals
    (ofString "q",pState.locals.lookup (ofString "q")))}
  let post := {qPost with locals := (HolFiniteMapExact.resVarEq qPost.locals
    (ofString "p",state.locals.lookup (ofString "p")))}
  have pLocal : pState.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [pState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have namesNP : ofString "p" ≠ ofString "n" := by decide
  have namesQP : ofString "q" ≠ ofString "p" := by decide
  have nLocal : pState.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [pState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namesNP,sizeLocal]
  have pAtQ : qState.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [qState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namesQP,pLocal]
  have qLocal : qState.locals.lookup (ofString "q") = some (.val (.word (allocationEnd pointer size))) := by
    simp [qState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have finish := evaluate_allocationFinish qState pointer (allocationEnd pointer size) pointer pAtQ qLocal heapGlobal finishBound
  have qRun : evaluateHOLFiniteState pState (.dec (ofString "q") .one allocationEndExpression allocationFinish) =
      (some (.returned (.val (.word pointer))),qPost) := by
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [eval_allocationEndExpression pState pointer size pLocal nLocal]
    have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (allocationEnd pointer size)))) = true := by
      simp [shapeEqHOL,shapeOfHOLExact]
    dsimp only
    rw [if_pos shapeOk,finish]
  have guard := eval_allocationRequestCheck pState pointer size pLocal nLocal request
  have check : evaluateHOLFiniteState pState
      (.ite allocationRequestCheck (.call (some (none,none)) (ofString "trap_with") [.const 1]) .skip) =
        (none,pState) := by
    rw [evaluateHOLFiniteState_ite,guard]
    simp [evaluateHOLFiniteState_skip]
  have afterPointer : evaluateHOLFiniteState pState allocationAfterPointer =
      (some (.returned (.val (.word pointer))),qPost) := evaluate_seq_none check qRun
  refine ⟨post,?_,?_,rfl,rfl,?_,?_,?_,?_,?_⟩
  · rw [source_alloc_body,evaluateHOLFiniteState_dec_total]
    dsimp only
    have initial : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) (.var .global (ofString "heap_ptr")) =
          some (.val (.word pointer)) := heapGlobal
    rw [initial]
    have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word pointer))) = true := by
      simp [shapeEqHOL,shapeOfHOLExact]
    dsimp only
    rw [if_pos shapeOk,afterPointer]
  · simp [post,qPost,returned,emptyLocalsHOLFinite,setKvarHOLFinite,setGlobalHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE]
  all_goals simp only [post,qPost,returned,emptyLocalsHOLFinite,setKvarHOLFinite,setGlobalHOLFinite,
    qState,pState,setVarHOLFinite]

#print axioms evaluate_source_alloc_success
end InitECandidate.Runtime
