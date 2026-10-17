import InitECandidate.Runtime.RlpValidationPop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpValidationPushStores : ProgHOL 64 :=
  match rlpValidationListPush with | .decCall _ _ _ _ body => body | _ => .skip

def rlpValidationPushUpdates : ProgHOL 64 :=
  match rlpValidationPushStores with | .seq _ (.seq _ (.seq _ body)) => body | _ => .skip

theorem source_rlpValidation_push_updates : rlpValidationPushUpdates =
    .seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
      (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
        (.assign .local (ofString "end") (.var .local (ofString "after")))) := by
  simp only [rlpValidationPushUpdates,rlpValidationPushStores,rlpValidationListPush,rlpValidationAfterHeader,
    rlpValidationHeaderContinuation,rlpValidationHeaderCall,rlpValidationStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Once a list continuation record is saved, the original assignments enter
its payload interval and make the record the stack top, without source ticks. -/
theorem evaluate_rlpValidation_push_updates {F : Type} (state : PanSemStateFiniteExact 64 F)
    (oldTop position stop record payload after : BitVec 64)
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word oldTop)))
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (recordLocal : state.locals.lookup (ofString "rec") = some (.val (.word record)))
    (payloadLocal : state.locals.lookup (ofString "payload") = some (.val (.word payload)))
    (afterLocal : state.locals.lookup (ofString "after") = some (.val (.word after))) :
    evaluateHOLFiniteState state rlpValidationPushUpdates =
      (none,setVarHOLFinite (ofString "end") (.val (.word after))
        (setVarHOLFinite (ofString "pos") (.val (.word payload))
          (setVarHOLFinite (ofString "top") (.val (.word record)) state))) := by
  let first := setVarHOLFinite (ofString "top") (.val (.word record)) state
  let second := setVarHOLFinite (ofString "pos") (.val (.word payload)) first
  have one : evaluateHOLFiniteState state (.assign .local (ofString "top") (.var .local (ofString "rec"))) = (none,first) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,recordLocal,lookupKvarHOLExact,isValidValueHOLExact,
      topLocal,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL,first]
  have two : evaluateHOLFiniteState first (.assign .local (ofString "pos") (.var .local (ofString "payload"))) = (none,second) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      payloadLocal,lookupKvarHOLExact,isValidValueHOLExact,positionLocal,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL,second,
      show ofString "top" ≠ ofString "payload" by decide,show ofString "top" ≠ ofString "pos" by decide]
  have three : evaluateHOLFiniteState second (.assign .local (ofString "end") (.var .local (ofString "after"))) =
      (none,setVarHOLFinite (ofString "end") (.val (.word after)) second) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      afterLocal,lookupKvarHOLExact,isValidValueHOLExact,stopLocal,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL,
      show ofString "top" ≠ ofString "after" by decide,show ofString "pos" ≠ ofString "after" by decide,
      show ofString "top" ≠ ofString "end" by decide,show ofString "pos" ≠ ofString "end" by decide]
  rw [source_rlpValidation_push_updates,evaluateHOLFiniteState_seq_line780,one]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,two]
  exact three

#print axioms evaluate_rlpValidation_push_updates
end InitECandidate.Runtime
