import InitECandidate.Runtime.SourceDomainControlTransfer
import InitECandidate.Runtime.SourceDomainScopeTransfer
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- State-specific transfer is the induction predicate for the exact evaluator:
recursive hypotheses are required only at the source states actually reached. -/
def SourceDomainRunTransferAt {F : Type} (program : ProgHOL 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
 ∀(domain : BitVec 64→Prop),(∀address,s.memaddrs address→domain address)→
 ∀result post,evaluateHOLFiniteState s program=(result,post)→result≠some .error→
 evaluateHOLFiniteState {s with memaddrs:=domain} program=(result,{post with memaddrs:=domain})

theorem source_domain_transfer_at {program : ProgHOL 64} (transfer : SourceDomainRunTransfer program)
 {F : Type} (s : PanSemStateFiniteExact 64 F) : SourceDomainRunTransferAt program s:=transfer s

/-- The sequence induction step needs the second-command hypothesis only
after an actual normal completion of the first command. -/
theorem source_domain_transfer_seq_at {F : Type} (s : PanSemStateFiniteExact 64 F)
 (first second : ProgHOL 64) (firstTransfer : SourceDomainRunTransferAt first s)
 (secondTransfer : ∀middle,evaluateHOLFiniteState s first=(none,middle)→SourceDomainRunTransferAt second middle) :
 SourceDomainRunTransferAt (.seq first second) s := by
 intro domain subset result post run valid
 rw [evaluateHOLFiniteState_seq_line780] at run ⊢
 cases firstRun : evaluateHOLFiniteState s first with
 | mk firstResult middle=>
  rw [firstRun] at run
  cases firstResult with
  | none=>
   have transferred:=firstTransfer domain subset none middle firstRun (by simp)
   rw [transferred]
   have metadata:=evaluateHOLFiniteState_metadata s first
   rw [firstRun] at metadata
   have middleSubset : ∀address,middle.memaddrs address→domain address := by
    intro address accessible
    apply subset address
    rw [←metadata.2.1]
    exact accessible
   exact secondTransfer middle firstRun domain middleSubset result post run valid
  | some firstResult=>
   change (some firstResult,middle)=(result,post) at run
   have firstValid : some firstResult≠some .error:=by rw [(Prod.mk.inj run).1];exact valid
   have transferred:=firstTransfer domain subset (some firstResult) middle firstRun firstValid
   rw [transferred]
   cases run
   rfl

/-- The declaration induction step uses only the actual initializer value
and actual successful shape check to select its recursive body state. -/
theorem source_domain_transfer_dec_at {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64)
 (bodyTransfer : ∀value,
  @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) initializer=some value→
  shapeEqHOL shape (shapeOfHOLExact value)=true→
  SourceDomainRunTransferAt body (setVarHOLFinite name value s)) :
 SourceDomainRunTransferAt (.dec name shape initializer body) s := by
 intro domain subset result post run valid
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
     have widened:=bodyTransfer value actual fits domain subset bodyResult middle bodyRun bodyValid
     change evaluateHOLFiniteState (setVarHOLFinite name value {s with memaddrs:=domain}) body=
      (bodyResult,{middle with memaddrs:=domain}) at widened
     rw [widened]
     cases run
     rfl
  · rw [if_neg fits] at run
    exact False.elim (valid (Prod.mk.inj run).1.symm)


#print axioms source_domain_transfer_at
#print axioms source_domain_transfer_seq_at
#print axioms source_domain_transfer_dec_at

/-- Conditional induction needs a recursive hypothesis only for the actual
word-valued condition and the branch it selects in the source state. -/
theorem source_domain_transfer_ite_at {F : Type} (s : PanSemStateFiniteExact 64 F)
 (condition : ExpHOL 64) (yes no : ProgHOL 64)
 (branchTransfer : ∀w : BitVec 64,
  @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) condition=some (.val (.word w))→
  SourceDomainRunTransferAt (if w=0 then no else yes) s) :
 SourceDomainRunTransferAt (.ite condition yes no) s := by
 intro domain subset result post run valid
 rw [evaluateHOLFiniteState_ite] at run ⊢
 cases actual : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) condition with
 | none=>
  rw [actual] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some value=>
  rw [actual] at run
  rw [eval_source_domain_extend s domain subset condition value actual]
  cases value with
  | val word=>
   cases word with
   | word w=>
    dsimp only at run ⊢
    have selected:=branchTransfer w actual
    by_cases zero : w=0
    · rw [if_pos zero] at run ⊢
      simp only [if_pos zero] at selected
      exact selected domain subset result post run valid
    · rw [if_neg zero] at run ⊢
      simp only [if_neg zero] at selected
      exact selected domain subset result post run valid
  | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | nStruct name fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)

#print axioms source_domain_transfer_ite_at
end InitECandidate.Runtime
