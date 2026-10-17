import InitECandidate.Runtime.RlpValidationHeaderCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpValidationAfterHeader : ProgHOL 64 :=
  match rlpValidationHeaderContinuation with | .dec _ _ _ (.dec _ _ _ body) => body | _ => .skip

def rlpValidationListPush : ProgHOL 64 :=
  match rlpValidationAfterHeader with | .ite _ body _ => body | _ => .skip

theorem source_rlpValidation_header_continuation : rlpValidationHeaderContinuation =
    .dec (ofString "payload") .one
      (.op .add [.var .local (ofString "pos"),.rfield 0 (.var .local (ofString "h"))])
      (.dec (ofString "after") .one
        (.op .add [.var .local (ofString "payload"),.rfield 1 (.var .local (ofString "h"))]) rlpValidationAfterHeader) := by
  simp only [rlpValidationAfterHeader,rlpValidationHeaderContinuation,rlpValidationHeaderCall,rlpValidationStep,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpValidation_after_header : rlpValidationAfterHeader =
    .ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
      rlpValidationListPush (.assign .local (ofString "pos") (.var .local (ofString "after"))) := by
  simp only [rlpValidationAfterHeader,rlpValidationListPush,rlpValidationHeaderContinuation,
    rlpValidationHeaderCall,rlpValidationStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

noncomputable def rlpValidationNonListPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position header payload : BitVec 64) : PanSemStateFiniteExact 64 F :=
  let entered := setVarHOLFinite (ofString "after") (.val (.word (position + header + payload)))
    (setVarHOLFinite (ofString "payload") (.val (.word (position + header))) state)
  let advanced := setVarHOLFinite (ofString "pos") (.val (.word (position + header + payload))) entered
  let restored := {advanced with locals := HolFiniteMapExact.resVarEq advanced.locals (ofString "after",state.locals.lookup (ofString "after"))}
  {restored with locals := HolFiniteMapExact.resVarEq restored.locals (ofString "payload",state.locals.lookup (ofString "payload"))}

/-- The original non-list continuation advances the cursor without any call,
loop, memory write or source-clock debit. -/
theorem evaluate_rlpValidation_non_list {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position header payload : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (headerLocal : state.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word header),.val (.word payload),.val (.word 0)])) :
    evaluateHOLFiniteState state rlpValidationHeaderContinuation =
      (none,rlpValidationNonListPost state position header payload) := by
  let first := setVarHOLFinite (ofString "payload") (.val (.word (position + header))) state
  let second := setVarHOLFinite (ofString "after") (.val (.word (position + header + payload))) first
  let advanced := setVarHOLFinite (ofString "pos") (.val (.word (position + header + payload))) second
  have headerFirst : first.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word header),.val (.word payload),.val (.word 0)]) := by
    simpa [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "payload" ≠ ofString "h" by decide] using headerLocal
  have payloadFirst : first.locals.lookup (ofString "payload") = some (.val (.word (position + header))) := by
    simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have initial := eval_rlp_validator_payload state position header payload 0 positionLocal headerLocal
  have next := eval_rlp_validator_after first position header payload 0 payloadFirst headerFirst
  have branch : evaluateHOLFiniteState second rlpValidationAfterHeader = (none,advanced) := by
    rw [source_rlpValidation_after_header,evaluateHOLFiniteState_ite]
    have h : second.locals.lookup (ofString "h") =
        some (.rStruct [.val (.word header),.val (.word payload),.val (.word 0)]) := by
      simpa [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "after" ≠ ofString "h" by decide] using headerFirst
    have guard : @evalHOLExact 64 F _ second.toExact
        (fun address => Classical.propDecidable (second.memaddrs address))
        (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0)) = some (.val (.word 0)) := by
      simp [evalHOLExact,h,Compiler.Encoders.Asm.wordCmpHOL]
    rw [guard]
    simp only [if_true]
    simp [evaluateHOLFiniteState_assign,evalHOLExact,second,first,advanced,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,positionLocal,
      lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL,
      show ofString "after" ≠ ofString "pos" by decide,
      show ofString "payload" ≠ ofString "pos" by decide]
  have inner : evaluateHOLFiniteState first (.dec (ofString "after") .one
      (.op .add [.var .local (ofString "payload"),.rfield 1 (.var .local (ofString "h"))]) rlpValidationAfterHeader) =
      (none,{advanced with locals := HolFiniteMapExact.resVarEq advanced.locals (ofString "after",first.locals.lookup (ofString "after"))}) := by
    rw [evaluateHOLFiniteState_dec_total]
    simp only [next,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let result := evaluateHOLFiniteState second rlpValidationAfterHeader; _) = _
    rw [branch]
  rw [source_rlpValidation_header_continuation,evaluateHOLFiniteState_dec_total]
  simp only [initial,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState first (.dec (ofString "after") .one
    (.op .add [.var .local (ofString "payload"),.rfield 1 (.var .local (ofString "h"))]) rlpValidationAfterHeader);
    (result.1,{result.2 with locals := HolFiniteMapExact.resVarEq result.2.locals (ofString "payload",state.locals.lookup (ofString "payload"))})) = _
  dsimp only
  simp only [inner]
  simp [rlpValidationNonListPost,first,second,advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "payload" ≠ ofString "after" by decide]

theorem rlpValidation_non_list_post {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position header payload : BitVec 64) :
    let post := rlpValidationNonListPost state position header payload
    post.locals.lookup (ofString "pos") = some (.val (.word (position + header + payload))) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals := by
  refine ⟨?_,rfl,rfl,rfl⟩
  dsimp only [rlpValidationNonListPost]
  rw [restore_other_local _ _ (ofString "pos") _ (by decide)]
  rw [restore_other_local _ _ (ofString "pos") _ (by decide)]
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms rlpValidation_non_list_post
#print axioms evaluate_rlpValidation_non_list
end InitECandidate.Runtime
