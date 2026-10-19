import InitECandidate.Runtime.HtrRequestRecordFrameContract
import InitECandidate.Runtime.HtrRequestListStepBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def RequestStepFrame (program : ProgHOL 64) (cost : Nat) : Prop :=
  ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind pointer index size roots heap sha accelerator zeroHashes watched : BitVec 64),
    RequestStepLocals state kind pointer index size roots →
    HashMemoryLayout state sha accelerator zeroHashes heap (roots + index * (32#64)) watched →
    cost ≤ state.clock → evaluateHOLFiniteState state program = (none,post) →
    post.memory watched = state.memory watched ∧ post.globals = state.globals

theorem requestStep_increment_frame : RequestStepFrame htrRequestIncrement 0 := by
  intro F state post kind pointer index size roots heap sha accelerator zeroHashes watched locals layout budget run
  unfold htrRequestIncrement at run
  rw [evaluate_increment_local state (ofString "i") index locals.2.2.1] at run
  cases run
  exact ⟨rfl,rfl⟩

theorem requestStep_branch_frame (tag : BitVec 64) (function : MlS) (ticks : Nat)
    (contract : RequestRecordCallContract function ticks) (frameContract : RequestRecordFrameContract function ticks)
    (tail : ProgHOL 64) (cost : Nat) (frame : RequestStepFrame tail cost) :
    RequestStepFrame (.seq (htrRequestListBranch tag function) tail) (ticks + cost) := by
  intro F state post kind pointer index size roots heap sha accelerator zeroHashes watched locals layout budget run
  have first := htrRequestList_branch_bound state kind tag pointer index size roots heap function ticks contract
    locals.1 locals.2.1 locals.2.2.1 locals.2.2.2.1 locals.2.2.2.2 layout.atHeap layout.heapFits layout.code (by omega)
  obtain ⟨middle,normal,last⟩ := seq_normal_parts run
  have keep := first.2 middle normal
  have before := htrRequestList_branch_normal_frame state middle kind tag pointer index size roots heap sha accelerator zeroHashes watched
    function ticks frameContract layout locals.1 locals.2.1 locals.2.2.1 locals.2.2.2.1 locals.2.2.2.2 (by omega) normal
  have metadata := evaluateHOLFiniteState_metadata state (htrRequestListBranch tag function)
  rw [normal] at metadata
  have spent := first.1.1
  rw [normal] at spent
  have remaining : cost ≤ middle.clock := by
    change state.clock ≤ middle.clock + ticks at spent
    omega
  have after := frame middle post kind pointer index size roots heap sha accelerator zeroHashes watched
    ⟨(keep.2 _).trans locals.1,(keep.2 _).trans locals.2.1,(keep.2 _).trans locals.2.2.1,
      (keep.2 _).trans locals.2.2.2.1,(keep.2 _).trans locals.2.2.2.2⟩
    (layout.transfer before.2 metadata.1) remaining last
  exact ⟨after.1.trans before.1,after.2.trans before.2⟩

theorem htrRequestList_step_normal_frame : RequestStepFrame htrRequestListStep htrRequestStepCost := by
  exact requestStep_branch_frame 0 (ofString "htr_deposit") _ requestRecordCallContract_deposit requestRecordFrameContract_deposit _ _
    (requestStep_branch_frame 1 (ofString "htr_wdreq") _ requestRecordCallContract_wdreq requestRecordFrameContract_wdreq _ _
      (requestStep_branch_frame 2 (ofString "htr_cons") _ requestRecordCallContract_cons requestRecordFrameContract_cons _ _
        (requestStep_branch_frame 3 (ofString "htr_bdep") _ requestRecordCallContract_bdep requestRecordFrameContract_bdep _ _
          (requestStep_branch_frame 4 (ofString "htr_bexit") _ requestRecordCallContract_bexit requestRecordFrameContract_bexit _ _
            requestStep_increment_frame))))

#print axioms requestStep_increment_frame
#print axioms requestStep_branch_frame
#print axioms htrRequestList_step_normal_frame
end InitECandidate.Runtime
