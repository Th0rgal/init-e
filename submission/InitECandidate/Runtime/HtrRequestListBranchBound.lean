import InitECandidate.Runtime.HtrRequestListArguments
import InitECandidate.Runtime.HtrRequestRecordsReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def RequestRecordCallContract (function : MlS) (ticks : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64),
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)] →
    state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) → heap.toNat ≤ 33806089496 →
    state.code = originalRuntimeCode → ticks ≤ state.clock →
    RunBounded state (.call (some (none,none)) function arguments) ticks ∧
      ∀ post, evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,post) →
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))

theorem requestRecordCallContract_deposit : RequestRecordCallContract (ofString "htr_deposit") (htrDepositBodyCost + 1) := by
  intro F state arguments pointer out heap args hh cap code budget
  exact ⟨runBounded_htrDeposit_call state none arguments pointer out heap args hh cap code budget,
    fun post run => htrDeposit_call_normal_heap state post arguments pointer out heap args code hh run⟩

theorem requestRecordCallContract_wdreq : RequestRecordCallContract (ofString "htr_wdreq") (htrWdreqBodyCost + 1) := by
  intro F state arguments pointer out heap args hh cap code budget
  exact ⟨runBounded_htrWdreq_call state none arguments pointer out heap args hh cap code budget,
    fun post run => htrWdreq_call_normal_heap state post arguments pointer out heap args code hh run⟩

theorem requestRecordCallContract_cons : RequestRecordCallContract (ofString "htr_cons") (htrConsBodyCost + 1) := by
  intro F state arguments pointer out heap args hh cap code budget
  exact ⟨runBounded_htrCons_call state none arguments pointer out heap args hh cap code budget,
    fun post run => htrCons_call_normal_heap state post arguments pointer out heap args code hh run⟩

theorem requestRecordCallContract_bdep : RequestRecordCallContract (ofString "htr_bdep") (htrBdepBodyCost + 1) := by
  intro F state arguments pointer out heap args hh cap code budget
  exact ⟨runBounded_htrBdep_call state none arguments pointer out heap args hh cap code budget,
    fun post run => htrBdep_call_normal_heap state post arguments pointer out heap args code hh run⟩

theorem requestRecordCallContract_bexit : RequestRecordCallContract (ofString "htr_bexit") (htrBexitBodyCost + 1) := by
  intro F state arguments pointer out heap args hh cap code budget
  exact ⟨runBounded_htrBexit_call state none arguments pointer out heap args hh cap code budget,
    fun post run => htrBexit_call_normal_heap state post arguments pointer out heap args code hh run⟩

theorem htrRequestList_branch_evaluate {F : Type} (state : PanSemStateFiniteExact 64 F)
    (kind tag : BitVec 64) (function : MlS)
    (atKind : state.locals.lookup (ofString "kind") = some (.val (.word kind))) :
    evaluateHOLFiniteState state (htrRequestListBranch tag function) =
      if kind = tag then evaluateHOLFiniteState state (.call (some (none,none)) function htrRequestListArguments) else (none,state) := by
  rw [htrRequestListBranch,evaluateHOLFiniteState_ite,htrRequestList_kind_condition state kind tag atKind]
  by_cases same : kind = tag
  · simp [same,show (1 : BitVec 64) ≠ 0 by decide]
  · simp [same,evaluateHOLFiniteState_skip]

/-- Any one original request dispatch branch is bounded even when not selected;
a normal path restores the heap and preserves all caller locals. -/
theorem htrRequestList_branch_bound {F : Type} (state : PanSemStateFiniteExact 64 F)
    (kind tag pointer index size roots heap : BitVec 64) (function : MlS) (ticks : Nat)
    (contract : RequestRecordCallContract function ticks)
    (atKind : state.locals.lookup (ofString "kind") = some (.val (.word kind)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atSize : state.locals.lookup (ofString "sz") = some (.val (.word size)))
    (atRoots : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode) (budget : ticks ≤ state.clock) :
    RunBounded state (htrRequestListBranch tag function) ticks ∧
      ∀ post, evaluateHOLFiniteState state (htrRequestListBranch tag function) = (none,post) →
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
          ∀ key, post.locals.lookup key = state.locals.lookup key := by
  have args := htrRequestList_arguments state pointer index size roots atPointer atIndex atSize atRoots
  have call := contract state htrRequestListArguments (pointer + index * size) (roots + index * (32#64)) heap args hh cap code budget
  have evaluated := htrRequestList_branch_evaluate state kind tag function atKind
  constructor
  · unfold RunBounded
    rw [evaluated]
    by_cases same : kind = tag
    · rw [if_pos same]
      exact call.1
    · rw [if_neg same]
      exact ⟨Nat.le_add_right _ _,le_refl _,by simp⟩
  · intro post normal
    have heapKept : post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
      rw [evaluated] at normal
      by_cases same : kind = tag
      · rw [if_pos same] at normal
        exact call.2 post normal
      · rw [if_neg same] at normal
        obtain ⟨_,rfl⟩ := Prod.mk.inj normal
        exact hh
    refine ⟨heapKept,?_⟩
    intro key
    have kept := evaluate_avoidsLocal_flowing key (htrRequestListBranch tag function) rfl state
      (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using kept

#print axioms requestRecordCallContract_deposit
#print axioms requestRecordCallContract_wdreq
#print axioms requestRecordCallContract_cons
#print axioms requestRecordCallContract_bdep
#print axioms requestRecordCallContract_bexit
#print axioms htrRequestList_branch_evaluate
#print axioms htrRequestList_branch_bound
end InitECandidate.Runtime
