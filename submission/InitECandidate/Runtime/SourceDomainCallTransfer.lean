import InitECandidate.Runtime.SourceDomainTransferAt
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Ordinary-call induction, including local/global result assignment and
checked exception handlers. Recursive hypotheses concern only the actual
callee entry and the actual handler entry reached by the source execution. -/
theorem source_domain_transfer_call_at {F : Type} (s : PanSemStateFiniteExact 64 F)
 (info : Option (Option (VarKind×MlS) × Option (MlS×MlS×ProgHOL 64)))
 (function : MlS) (arguments : List (ExpHOL 64))
 (bodyTransfer : ∀values body callee returnShape,
  evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values→
  lookupCodeHOLFinite s.code.lookup function values=some (body,callee,returnShape)→s.clock≠0→
  SourceDomainRunTransferAt body (callEntryStateHOLFinite s callee))
 (handlerTransfer : ∀values body callee returnShape id value middle destination handlerId handlerVar handlerProgram shape,
  evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values→
  lookupCodeHOLFinite s.code.lookup function values=some (body,callee,returnShape)→s.clock≠0→
  evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body=(some (.exception id value),middle)→
  info=some (destination,some (handlerId,handlerVar,handlerProgram))→id=handlerId→
  s.eshapes.lookup id=some shape→shapeEqHOL (shapeOfHOLExact value) shape=true→
  isValidValueHOLExact s.toExact .local handlerVar value=true→
  SourceDomainRunTransferAt handlerProgram (setVarHOLFinite handlerVar value {middle with locals:=s.locals})) :
 SourceDomainRunTransferAt (.call info function arguments) s := by
 intro domain subset result post run valid
 rw [evaluateHOLFiniteState_call] at run ⊢
 cases args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments with
 | none=>
  rw [args] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some values=>
  rw [args] at run
  have wideArgs : evalListHOLFinite {s with memaddrs:=domain}
   (h:=fun a=>Classical.propDecidable (domain a)) arguments=some values := by
   rw [evalListHOLFinite_eq_toExact]
   apply eval_list_source_domain_extend s domain subset arguments values
   simpa only [evalListHOLFinite_eq_toExact] using args
  rw [wideArgs]
  dsimp only at run ⊢
  cases lookup : lookupCodeHOLFinite s.code.lookup function values with
  | none=>
   rw [lookup] at run
   exact False.elim (valid (Prod.mk.inj run).1.symm)
  | some data=>
   obtain ⟨body,callee,returnShape⟩:=data
   simp only [lookup] at run ⊢
   by_cases zero : s.clock=0
   · simp only [show ({s with memaddrs:=domain}).clock=s.clock from rfl,if_pos zero] at run ⊢
     cases run
     rfl
   · simp only [show ({s with memaddrs:=domain}).clock=s.clock from rfl,if_neg zero] at run ⊢
     cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
     | mk bodyResult middle=>
      rw [bodyRun] at run
      have bodyValid : bodyResult≠some .error := by
       intro failed
       rw [failed] at run
       exact valid (Prod.mk.inj run).1.symm
      have widened:=(bodyTransfer values body callee returnShape args lookup zero)
       domain subset bodyResult middle bodyRun bodyValid
      change evaluateHOLFiniteState (callEntryStateHOLFinite {s with memaddrs:=domain} callee) body=
       (bodyResult,{middle with memaddrs:=domain}) at widened
      rw [widened]
      have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
      rw [bodyRun] at metadata
      have middleSubset : ∀address,middle.memaddrs address→domain address := by
       intro address accessible
       apply subset address
       rw [←show middle.memaddrs=s.memaddrs from metadata.2.1]
       exact accessible
      cases bodyResult with
      | none=>exact False.elim (valid (Prod.mk.inj run).1.symm)
      | some bodyResult=>
       cases bodyResult with
       | «break»=>exact False.elim (valid (Prod.mk.inj run).1.symm)
       | «continue»=>exact False.elim (valid (Prod.mk.inj run).1.symm)
       | error=>exact False.elim (bodyValid rfl)
       | returned value=>
        dsimp only at run ⊢
        by_cases checked : shapeEqHOL (shapeOfHOLExact value) returnShape=true
        · rw [if_pos checked] at run ⊢
          cases info with
          | none=>cases run;rfl
          | some data=>
           obtain ⟨destination,handler⟩:=data
           cases destination with
           | none=>cases run;rfl
           | some data=>
            obtain ⟨kind,name⟩:=data
            have same : isValidValueHOLExact ({s with memaddrs:=domain}).toExact kind name value=
             isValidValueHOLExact s.toExact kind name value := by cases kind <;>rfl
            dsimp only at run ⊢
            rw [same]
            by_cases assignable : isValidValueHOLExact s.toExact kind name value=true
            · rw [if_pos assignable] at run ⊢
              cases run
              cases kind <;>rfl
            · rw [if_neg assignable] at run
              exact False.elim (valid (Prod.mk.inj run).1.symm)
        · rw [if_neg checked] at run
          exact False.elim (valid (Prod.mk.inj run).1.symm)
       | exception id value=>
        dsimp only at run ⊢
        cases info with
        | none=>cases run;rfl
        | some data=>
         obtain ⟨destination,handler⟩:=data
         cases handler with
         | none=>cases run;rfl
         | some data=>
          obtain ⟨handlerId,handlerVar,handlerProgram⟩:=data
          dsimp only at run ⊢
          by_cases matching : id=handlerId
          · rw [if_pos matching] at run ⊢
            cases installed : s.eshapes.lookup id with
            | none=>
             rw [installed] at run
             exact False.elim (valid (Prod.mk.inj run).1.symm)
            | some shape=>
             simp only [installed] at run ⊢
             have same : isValidValueHOLExact ({s with memaddrs:=domain}).toExact .local handlerVar value=
              isValidValueHOLExact s.toExact .local handlerVar value:=rfl
             rw [same]
             by_cases checked : (shapeEqHOL (shapeOfHOLExact value) shape &&
              isValidValueHOLExact s.toExact .local handlerVar value)=true
             · rw [if_pos checked] at run ⊢
               have checks : shapeEqHOL (shapeOfHOLExact value) shape=true ∧
                isValidValueHOLExact s.toExact .local handlerVar value=true := by
                simpa only [Bool.and_eq_true] using checked
               exact (handlerTransfer values body callee returnShape id value middle destination
                handlerId handlerVar handlerProgram shape args lookup zero bodyRun rfl matching installed checks.1 checks.2)
                domain middleSubset result post run valid
             · rw [if_neg checked] at run
               exact False.elim (valid (Prod.mk.inj run).1.symm)
          · rw [if_neg matching] at run ⊢
            cases run
            rfl
       | timeOut=>cases run;rfl
       | finalFfi event=>cases run;rfl

#print axioms source_domain_transfer_call_at
end InitECandidate.Runtime
