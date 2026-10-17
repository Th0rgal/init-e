import InitECandidate.Runtime.RlpValidationCursor
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpValidationStep : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn__rlp_validate_items_body with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq (.while _ body) _)))) => body
  | _ => .skip

def rlpValidationHeaderCall : ProgHOL 64 :=
  match rlpValidationStep with | .ite _ _ body => body | _ => .skip

def rlpValidationHeaderContinuation : ProgHOL 64 :=
  match rlpValidationHeaderCall with | .decCall _ _ _ _ body => body | _ => .skip

theorem source_rlpValidation_header_call : rlpValidationHeaderCall =
    .decCall (ofString "h") (.comb [.one,.one,.one]) (ofString "rlp_item_header")
      [.var .local (ofString "pos"),.op .sub [.var .local (ofString "end"),.var .local (ofString "pos")]]
      rlpValidationHeaderContinuation := by
  simp only [rlpValidationHeaderCall,rlpValidationHeaderContinuation,rlpValidationStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Normal completion of the original validator header call exposes the real
continuation with exact header fields and a strictly advancing bounded cursor. -/
theorem evaluate_rlpValidation_header_call_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (ordered : position.toNat ≤ stop.toNat)
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpValidationHeaderCall = (none,post)) :
    ∃ (header payload kind : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      (kind = 0 ∨ kind = 1) ∧ position.toNat < (position + header + payload).toNat ∧
      (position + header + payload).toNat ≤ stop.toNat ∧
      stop.toNat - (position + header + payload).toNat < stop.toNat - position.toNat ∧
      (kind = 1 → payload.toNat < stop.toNat - position.toNat) ∧ ready.locals = state.locals ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "h")
        (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) ready)
        rlpValidationHeaderContinuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "h",state.locals.lookup (ofString "h"))} := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "pos"),.op .sub [.var .local (ofString "end"),.var .local (ofString "pos")]] =
      some [.val (.word position),.val (.word (stop - position))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,positionLocal,stopLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpValidation_header_call] at run
  obtain ⟨value,ready,output,valid,locals,tail,restored⟩ := evaluate_rlpHeader_decCall_normal state post (ofString "h")
    [.var .local (ofString "pos"),.op .sub [.var .local (ofString "end"),.var .local (ofString "pos")]]
    rlpValidationHeaderContinuation position (stop - position) args code ticks run
  obtain ⟨header,payload,kind,shape,flag,advances,fits,decreases,nested⟩ :=
    rlp_header_progress_cursor value position stop ordered valid
  subst value
  exact ⟨header,payload,kind,ready,output,flag,advances,fits,decreases,nested,locals,tail,restored⟩

#print axioms evaluate_rlpValidation_header_call_normal
end InitECandidate.Runtime
