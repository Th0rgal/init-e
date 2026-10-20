import InitECandidate.Runtime.SourceDomainTransferAt
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Declaration-call induction follows the actual installed callee and its
checked return into the actual scoped continuation. Recursive hypotheses are
state-specific; no future-callee runtime/frame contract is assumed. -/
theorem source_domain_transfer_decCall_at {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (bodyTransfer : ∀values body callee returnShape,
  evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values→
  lookupCodeHOLFinite s.code.lookup function values=some (body,callee,returnShape)→s.clock≠0→
  SourceDomainRunTransferAt body (callEntryStateHOLFinite s callee))
 (tailTransfer : ∀values body callee returnShape returned middle,
  evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values→
  lookupCodeHOLFinite s.code.lookup function values=some (body,callee,returnShape)→s.clock≠0→
  evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body=(some (.returned returned),middle)→
  shapeEqHOL (shapeOfHOLExact returned) shape=true→shapeEqHOL (shapeOfHOLExact returned) returnShape=true→
  SourceDomainRunTransferAt tail (setVarHOLFinite name returned {middle with locals:=s.locals})) :
 SourceDomainRunTransferAt (.decCall name shape function arguments tail) s := by
 intro domain subset result post run valid
 rw [evaluateHOLFiniteState_decCall_total] at run ⊢
 simp only [fixClockHOLFinite_evaluate] at run ⊢
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
      have remaining:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
      rw [bodyRun] at remaining
      dsimp only at remaining
      have remainingWide : middle.clock≤(callEntryStateHOLFinite {s with memaddrs:=domain} callee).clock:=remaining
      simp only [fixClockHOLFinite,if_neg (Nat.not_lt.mpr remaining),if_neg (Nat.not_lt.mpr remainingWide)] at run ⊢
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
       | returned returned=>
        dsimp only at run ⊢
        by_cases checked : (shapeEqHOL (shapeOfHOLExact returned) shape &&
         shapeEqHOL (shapeOfHOLExact returned) returnShape)=true
        · rw [if_pos checked] at run ⊢
          have checks : shapeEqHOL (shapeOfHOLExact returned) shape=true ∧
           shapeEqHOL (shapeOfHOLExact returned) returnShape=true := by
           simpa only [Bool.and_eq_true] using checked
          cases tailRun : evaluateHOLFiniteState (setVarHOLFinite name returned {middle with locals:=s.locals}) tail with
          | mk tailResult output=>
           rw [tailRun] at run
           have tailValid : tailResult≠some .error:=by
            have same : tailResult=result:=(Prod.mk.inj run).1
            rw [same];exact valid
           have tailWide:=(tailTransfer values body callee returnShape returned middle args lookup zero bodyRun checks.1 checks.2)
            domain middleSubset tailResult output tailRun tailValid
           change evaluateHOLFiniteState
            (setVarHOLFinite name returned {{middle with memaddrs:=domain} with locals:=s.locals}) tail=
             (tailResult,{output with memaddrs:=domain}) at tailWide
           rw [tailWide]
           cases run
           rfl
        · rw [if_neg checked] at run
          exact False.elim (valid (Prod.mk.inj run).1.symm)
       | timeOut=>cases run;rfl
       | exception id value=>cases run;rfl
       | finalFfi event=>cases run;rfl

#print axioms source_domain_transfer_decCall_at
end InitECandidate.Runtime
