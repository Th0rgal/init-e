import InitECandidate.Runtime.HtrRequestListBranchBound
import InitECandidate.Runtime.HtabDelBound
import InitECandidate.Runtime.HtabGrowRehash
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def RequestStepLocals {F : Type} (state : PanSemStateFiniteExact 64 F) (kind pointer index size roots : BitVec 64) : Prop :=
  state.locals.lookup (ofString "kind") = some (.val (.word kind)) ∧
  state.locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
  state.locals.lookup (ofString "i") = some (.val (.word index)) ∧
  state.locals.lookup (ofString "sz") = some (.val (.word size)) ∧
  state.locals.lookup (ofString "roots") = some (.val (.word roots))

def RequestStepBound (program : ProgHOL 64) (cost : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (kind pointer index size roots heap : BitVec 64),
    RequestStepLocals state kind pointer index size roots →
    state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) → heap.toNat ≤ 33806089496 →
    state.code = originalRuntimeCode → cost ≤ state.clock →
    RunBounded state program cost ∧
      ∀ post, evaluateHOLFiniteState state program = (none,post) →
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
        post.locals.lookup (ofString "i") = some (.val (.word (index + (1#64)))) ∧
        ∀ key, key ≠ ofString "i" → post.locals.lookup key = state.locals.lookup key

def htrRequestIncrement : ProgHOL 64 :=
  .assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])

theorem requestStep_increment_bound : RequestStepBound htrRequestIncrement 0 := by
  intro F state kind pointer index size roots heap locals hh cap code budget
  have run := evaluate_increment_local state (ofString "i") index locals.2.2.1
  constructor
  · exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) code budget
  · intro post normal
    unfold htrRequestIncrement at normal
    rw [run] at normal
    cases normal
    refine ⟨hh,?_,?_⟩
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro key different
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

theorem requestStep_branch_lift (tag : BitVec 64) (function : MlS) (ticks : Nat)
    (contract : RequestRecordCallContract function ticks) (tail : ProgHOL 64) (cost : Nat)
    (bounded : RequestStepBound tail cost) :
    RequestStepBound (.seq (htrRequestListBranch tag function) tail) (ticks + cost) := by
  intro F state kind pointer index size roots heap locals hh cap code budget
  have branch := htrRequestList_branch_bound state kind tag pointer index size roots heap function ticks contract
    locals.1 locals.2.1 locals.2.2.1 locals.2.2.2.1 locals.2.2.2.2 hh cap code (by omega)
  have after (middle : PanSemStateFiniteExact 64 F)
      (normal : evaluateHOLFiniteState state (htrRequestListBranch tag function) = (none,middle))
      (installed : middle.code = state.code) (remaining : cost ≤ middle.clock) := by
    have frame := branch.2 middle normal
    exact bounded middle kind pointer index size roots heap
      ⟨(frame.2 _).trans locals.1,(frame.2 _).trans locals.2.1,(frame.2 _).trans locals.2.2.1,
        (frame.2 _).trans locals.2.2.2.1,(frame.2 _).trans locals.2.2.2.2⟩ frame.1 cap (installed.trans code) remaining
  constructor
  · exact RunBounded.seq branch.1 budget (fun middle normal installed remaining => (after middle normal installed remaining).1)
  · intro post normal
    obtain ⟨middle,first,last⟩ := seq_normal_parts normal
    have meta' := evaluateHOLFiniteState_metadata state (htrRequestListBranch tag function)
    rw [first] at meta'
    have spent := branch.1.1
    rw [first] at spent
    have result := (after middle first meta'.1 (by change state.clock ≤ middle.clock + ticks at spent; omega)).2 post last
    exact ⟨result.1,result.2.1,fun key different => (result.2.2 key different).trans ((branch.2 middle first).2 key)⟩

def htrRequestStepCost4 : Nat := (htrBexitBodyCost + 1) + 0
def htrRequestStepCost3 : Nat := (htrBdepBodyCost + 1) + htrRequestStepCost4
def htrRequestStepCost2 : Nat := (htrConsBodyCost + 1) + htrRequestStepCost3
def htrRequestStepCost1 : Nat := (htrWdreqBodyCost + 1) + htrRequestStepCost2
def htrRequestStepCost : Nat := (htrDepositBodyCost + 1) + htrRequestStepCost1

theorem htrRequestList_step_bound : RequestStepBound htrRequestListStep htrRequestStepCost := by
  exact requestStep_branch_lift 0 (ofString "htr_deposit") _ requestRecordCallContract_deposit _ _
    (requestStep_branch_lift 1 (ofString "htr_wdreq") _ requestRecordCallContract_wdreq _ _
      (requestStep_branch_lift 2 (ofString "htr_cons") _ requestRecordCallContract_cons _ _
        (requestStep_branch_lift 3 (ofString "htr_bdep") _ requestRecordCallContract_bdep _ _
          (requestStep_branch_lift 4 (ofString "htr_bexit") _ requestRecordCallContract_bexit _ _ requestStep_increment_bound))))

#print axioms requestStep_increment_bound
#print axioms requestStep_branch_lift
#print axioms htrRequestList_step_bound
end InitECandidate.Runtime
