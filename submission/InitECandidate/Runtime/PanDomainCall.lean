import InitECandidate.Runtime.PanDomainRecursive
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem panDomainMono_call {F : Type} (s : PanSemStateFiniteExact 64 F)
    (info : Option (Option (VarKind×MlS)×Option (MlS×MlS×ProgHOL 64))) (function : MlS) (arguments : List (ExpHOL 64))
    (bodyIH : ∀ args body callee returnShape,
      @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some args→
      lookupCodeHOLFinite s.code.lookup function args=some (body,callee,returnShape)→s.clock≠0→
      PanDomainMonoAt body (callEntryStateHOLFinite s callee))
    (handlerIH : ∀ args body callee returnShape post exceptionId value destination handlerId handlerVar handlerProgram shape,
      @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some args→
      lookupCodeHOLFinite s.code.lookup function args=some (body,callee,returnShape)→s.clock≠0→
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body=(some (.exception exceptionId value),post)→
      info=some (destination,some (handlerId,handlerVar,handlerProgram))→exceptionId=handlerId→
      s.eshapes.lookup exceptionId=some shape→shapeOfHOLExact value=shape→isValidValueHOLExact s.toExact .local handlerVar value=true→
      PanDomainMonoAt handlerProgram (setVarHOLFinite handlerVar value {post with locals:=s.locals})) :
    PanDomainMonoAt (.call info function arguments) s := by
  classical
  intro domain subset valid
  simp only [evaluateHOLFiniteState_call s info function arguments,evaluateHOLFiniteState_call {s with memaddrs:=domain} info function arguments] at valid ⊢
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
            | returned value =>
              by_cases shapeOk : shapeEqHOL (shapeOfHOLExact value) returnShape=true
              · simp only [shapeOk,if_true] at valid ⊢
                cases info with
                | none => rfl
                | some pair =>
                  obtain ⟨destination,handler⟩:=pair
                  cases destination with
                  | none => rfl
                  | some destination =>
                    obtain ⟨kind,name⟩:=destination
                    have validEq : isValidValueHOLExact {s with memaddrs:=domain}.toExact kind name value=isValidValueHOLExact s.toExact kind name value := by cases kind <;>rfl
                    simp only [validEq]
                    by_cases allowed : isValidValueHOLExact s.toExact kind name value=true
                    · simp only [allowed,if_true]
                      cases kind <;>rfl
                    · simp [allowed] at valid
              · simp [shapeOk] at valid
            | exception exceptionId value =>
              cases infoEq : info with
              | none => rfl
              | some pair =>
                obtain ⟨destination,handler⟩:=pair
                cases handlerEq : handler with
                | none => rfl
                | some triple =>
                  obtain ⟨handlerId,handlerVar,handlerProgram⟩:=triple
                  simp only [infoEq,handlerEq] at valid ⊢
                  by_cases same : exceptionId=handlerId
                  · simp only [if_pos same] at valid ⊢
                    cases shapeRun : s.eshapes.lookup exceptionId with
                    | none => simp only [shapeRun] at valid;exact False.elim (valid rfl)
                    | some shape =>
                      simp only [shapeRun] at valid ⊢
                      have validEq : isValidValueHOLExact {s with memaddrs:=domain}.toExact .local handlerVar value=isValidValueHOLExact s.toExact .local handlerVar value := rfl
                      simp only [validEq]
                      by_cases allowed : (shapeEqHOL (shapeOfHOLExact value) shape &&isValidValueHOLExact s.toExact .local handlerVar value)=true
                      · simp only [allowed,if_true] at valid ⊢
                        have parts : shapeEqHOL (shapeOfHOLExact value) shape=true ∧isValidValueHOLExact s.toExact .local handlerVar value=true := by simpa only [Bool.and_eq_true] using allowed
                        have handlerBound:=handlerIH args body callee returnShape post exceptionId value destination handlerId handlerVar handlerProgram shape argsRun lookup zero run (by simpa only [handlerEq] using infoEq) same shapeRun ((shapeEqHOL_eq_true _ _).mp parts.1) parts.2
                        exact handlerBound domain postSubset valid
                      · simp [allowed] at valid
                  · simp only [if_neg same,emptyLocalsHOLFinite]
#print axioms panDomainMono_call
end InitECandidate.Runtime
