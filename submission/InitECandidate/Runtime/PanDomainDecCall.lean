import InitECandidate.Runtime.PanDomainCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem panDomainMono_decCall {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (bodyIH : ∀ args body callee returnShape,
      @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some args→
      lookupCodeHOLFinite s.code.lookup function args=some (body,callee,returnShape)→s.clock≠0→
      PanDomainMonoAt body (callEntryStateHOLFinite s callee))
    (continuationIH : ∀ args body callee returnShape post value,
      @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some args→
      lookupCodeHOLFinite s.code.lookup function args=some (body,callee,returnShape)→s.clock≠0→
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body=(some (.returned value),post)→
      shapeOfHOLExact value=shape→shapeOfHOLExact value=returnShape→
      PanDomainMonoAt continuation (setVarHOLFinite name value {post with locals:=s.locals})) :
    PanDomainMonoAt (.decCall name shape function arguments continuation) s := by
  classical
  intro domain subset valid
  simp only [evaluateHOLFiniteState_decCall_fixClockRewrite s name shape function arguments continuation,evaluateHOLFiniteState_decCall_fixClockRewrite {s with memaddrs:=domain} name shape function arguments continuation] at valid ⊢
  cases argsRun : @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) arguments with
  | none => simp only [argsRun] at valid;exact False.elim (valid rfl)
  | some args =>
    have argsNext:=evalListHOLFinite_memaddrs_mono s domain subset arguments args argsRun
    simp only [argsRun] at valid ⊢
    simp only [argsNext]
    cases lookup : lookupCodeHOLFinite s.code.lookup function args with
    | none => simp only [lookup] at valid;exact False.elim (valid rfl)
    | some entry =>
      obtain ⟨body,callee,returnShape⟩:=entry
      simp only [lookup] at valid ⊢
      by_cases zero : s.clock=0
      · simp only [zero,if_pos,emptyLocalsHOLFinite]
      · simp only [if_neg zero] at valid ⊢
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk result post =>
          have bodyNoError : result≠some .error := by
            intro bad
            simp only [run,bad] at valid
            exact valid rfl
          have bodyNext:=bodyIH args body callee returnShape argsRun lookup zero domain subset (by simpa only [run] using bodyNoError)
          simp only [run] at bodyNext
          change evaluateHOLFiniteState (callEntryStateHOLFinite {s with memaddrs:=domain} callee) body=_ at bodyNext
          simp only [run,bodyNext] at valid ⊢
          have postSubset : ∀address,post.memaddrs address→domain address := by
            have domainEq : post.memaddrs=s.memaddrs := by
              have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
              rw [run] at metadata
              exact metadata.2.1
            simpa only [domainEq] using subset
          cases result with
          | none => exact False.elim (valid rfl)
          | some result => cases result with
            | «break» => exact False.elim (valid rfl)
            | «continue» => exact False.elim (valid rfl)
            | error => exact False.elim (bodyNoError rfl)
            | timeOut => rfl
            | finalFfi event => rfl
            | exception id value => rfl
            | returned value =>
              by_cases allowed : (shapeEqHOL (shapeOfHOLExact value) shape &&shapeEqHOL (shapeOfHOLExact value) returnShape)=true
              · simp only [allowed,if_true] at valid ⊢
                have parts : shapeEqHOL (shapeOfHOLExact value) shape=true ∧shapeEqHOL (shapeOfHOLExact value) returnShape=true := by simpa only [Bool.and_eq_true] using allowed
                have continuationNext:=continuationIH args body callee returnShape post value argsRun lookup zero run ((shapeEqHOL_eq_true _ _).mp parts.1) ((shapeEqHOL_eq_true _ _).mp parts.2) domain postSubset valid
                change evaluateHOLFiniteState (setVarHOLFinite name value {post with locals:=s.locals,memaddrs:=domain}) continuation=_ at continuationNext
                rw [continuationNext]
              · simp [allowed] at valid
#print axioms panDomainMono_decCall
end InitECandidate.Runtime
