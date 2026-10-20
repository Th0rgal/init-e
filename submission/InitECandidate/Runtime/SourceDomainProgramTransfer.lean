import InitECandidate.Runtime.SourceDomainExpressionTransfer
import InitECandidate.Runtime.PanEvaluationMetadata
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A successful source run is unchanged when its ordinary-memory domain is
extended. Only the address predicate differs in the final state. The actual
source error outcome is excluded; no program-wide transfer is assumed here. -/
def SourceDomainRunTransfer (program : ProgHOL 64) : Prop :=
 ∀{F : Type} (s : PanSemStateFiniteExact 64 F) (domain : BitVec 64→Prop),
 (∀address,s.memaddrs address→domain address)→
 ∀result post,evaluateHOLFiniteState s program=(result,post)→result≠some .error→
 evaluateHOLFiniteState {s with memaddrs:=domain} program=(result,{post with memaddrs:=domain})

theorem source_domain_transfer_skip : SourceDomainRunTransfer .skip := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_skip] at run ⊢
 cases run
 rfl

/-- The actual returned value is preserved even if the expression reads
ordinary memory, because every successful read persists in the larger domain. -/
theorem source_domain_transfer_return (expression : ExpHOL 64) :
 SourceDomainRunTransfer (.return expression) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_return] at run ⊢
 cases actual : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
 | none=>
  rw [actual] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some value=>
  rw [actual] at run
  rw [eval_source_domain_extend s domain subset expression value actual]
  dsimp only at run
  by_cases fits : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value)≤32
  · rw [if_pos fits] at run
    simp only [show ({s with memaddrs:=domain}).structs=s.structs from rfl,if_pos fits]
    cases run
    rfl
  · rw [if_neg fits] at run
    exact False.elim (valid (Prod.mk.inj run).1.symm)

/-- Transfer composes through the real sequence evaluator. A non-error
sequence either completes its first command normally and runs its second, or
propagates the first command's unchanged non-error result. -/
theorem source_domain_transfer_seq {first second : ProgHOL 64}
 (firstTransfer : SourceDomainRunTransfer first) (secondTransfer : SourceDomainRunTransfer second) :
 SourceDomainRunTransfer (.seq first second) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_seq_line780] at run ⊢
 cases firstRun : evaluateHOLFiniteState s first with
 | mk firstResult middle=>
  rw [firstRun] at run
  cases firstResult with
  | none=>
   have transferred:=firstTransfer s domain subset none middle firstRun (by simp)
   rw [transferred]
   have metadata:=evaluateHOLFiniteState_metadata s first
   rw [firstRun] at metadata
   have middleSubset : ∀address,middle.memaddrs address→domain address := by
    intro address accessible
    apply subset address
    rw [←metadata.2.1]
    exact accessible
   exact secondTransfer middle domain middleSubset result post run valid
  | some firstResult=>
   change (some firstResult,middle)=(result,post) at run
   have firstValid : some firstResult≠some .error:=by rw [(Prod.mk.inj run).1];exact valid
   have transferred:=firstTransfer s domain subset (some firstResult) middle firstRun firstValid
   rw [transferred]
   cases run
   rfl

#print axioms source_domain_transfer_skip
#print axioms source_domain_transfer_return
#print axioms source_domain_transfer_seq
end InitECandidate.Runtime
