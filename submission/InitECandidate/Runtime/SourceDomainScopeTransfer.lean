import InitECandidate.Runtime.SourceDomainProgramTransfer
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A scoped declaration preserves its actual initializer, body result and
lexical restoration while only the ordinary-memory domain is enlarged. -/
theorem source_domain_transfer_dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
 {body : ProgHOL 64} (bodyTransfer : SourceDomainRunTransfer body) :
 SourceDomainRunTransfer (.dec name shape initializer body) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_dec_total] at run ⊢
 dsimp only at run ⊢
 cases actual : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) initializer with
 | none=>
  rw [actual] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some value=>
  rw [actual] at run
  rw [eval_source_domain_extend s domain subset initializer value actual]
  dsimp only at run ⊢
  by_cases fits : shapeEqHOL shape (shapeOfHOLExact value)=true
  · rw [if_pos fits] at run ⊢
    cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite name value s) body with
    | mk bodyResult middle=>
     rw [bodyRun] at run
     have bodyValid : bodyResult≠some .error:=by
      have same : bodyResult=result:=(Prod.mk.inj run).1
      rw [same];exact valid
     have widened:=bodyTransfer (setVarHOLFinite name value s) domain subset bodyResult middle bodyRun bodyValid
     change evaluateHOLFiniteState (setVarHOLFinite name value {s with memaddrs:=domain}) body=
      (bodyResult,{middle with memaddrs:=domain}) at widened
     rw [widened]
     cases run
     rfl
  · rw [if_neg fits] at run
    exact False.elim (valid (Prod.mk.inj run).1.symm)

/-- Raising a real checked exception preserves its value, identifier and state. -/
theorem source_domain_transfer_raise (name : MlS) (expression : ExpHOL 64) :
 SourceDomainRunTransfer (.raise name expression) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_raise] at run ⊢
 cases installed : s.eshapes.lookup name with
 | none=>
  rw [installed] at run
  cases actual : @evalHOLExact 64 F _ s.toExact
   (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
  | none=>rw [actual] at run;exact False.elim (valid (Prod.mk.inj run).1.symm)
  | some value=>rw [actual] at run;exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some shape=>
  simp only [installed] at run ⊢
  cases actual : @evalHOLExact 64 F _ s.toExact
   (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
  | none=>
   rw [actual] at run
   exact False.elim (valid (Prod.mk.inj run).1.symm)
  | some value=>
   rw [actual] at run
   rw [eval_source_domain_extend s domain subset expression value actual]
   dsimp only at run ⊢
   by_cases fits : shapeOfHOLExact value=shape ∧sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value)≤32
   · rw [if_pos fits] at run
     simp only [show ({s with memaddrs:=domain}).structs=s.structs from rfl,if_pos fits]
     cases run
     rfl
   · rw [if_neg fits] at run
     exact False.elim (valid (Prod.mk.inj run).1.symm)

theorem source_domain_transfer_break : SourceDomainRunTransfer .break := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_break] at run ⊢
 cases run
 rfl

theorem source_domain_transfer_continue : SourceDomainRunTransfer .continue := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_continue] at run ⊢
 cases run
 rfl

theorem source_domain_transfer_annot (name value : MlS) : SourceDomainRunTransfer (.annot name value) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_annot] at run ⊢
 cases run
 rfl

/-- Clock consumption and timeout are identical under a domain-only update. -/
theorem source_domain_transfer_tick : SourceDomainRunTransfer .tick := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_tick] at run ⊢
 by_cases zero : s.clock=0
 · simp only [show ({s with memaddrs:=domain}).clock=s.clock from rfl,if_pos zero] at run ⊢
   cases run
   rfl
 · simp only [show ({s with memaddrs:=domain}).clock=s.clock from rfl,if_neg zero] at run ⊢
   cases run
   rfl

#print axioms source_domain_transfer_dec
#print axioms source_domain_transfer_raise
#print axioms source_domain_transfer_break
#print axioms source_domain_transfer_continue
#print axioms source_domain_transfer_annot
#print axioms source_domain_transfer_tick

/-- A primitive receives the same actual argument values and preserves its
pure result and local shape check in the enlarged ordinary-memory domain. -/
theorem source_domain_transfer_primitive (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL 64)) :
 SourceDomainRunTransfer (.primitive name operator arguments) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_primitive] at run ⊢
 cases actual : @evalListHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) arguments with
 | none=>
  rw [actual] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some values=>
  rw [actual] at run
  rw [eval_list_source_domain_extend s domain subset arguments values actual]
  dsimp only at run ⊢
  cases primitive : panPrimopHOLExact operator values with
  | none=>
   rw [primitive] at run
   exact False.elim (valid (Prod.mk.inj run).1.symm)
  | some value=>
   simp only [primitive] at run ⊢
   have same : isValidValueHOLFinite ({s with memaddrs:=domain}) .local name value=
    isValidValueHOLFinite s .local name value:=rfl
   rw [same]
   by_cases checked : isValidValueHOLFinite s .local name value=true
   · rw [if_pos checked] at run ⊢
     cases run
     rfl
   · rw [if_neg checked] at run
     exact False.elim (valid (Prod.mk.inj run).1.symm)

#print axioms source_domain_transfer_primitive
end InitECandidate.Runtime
