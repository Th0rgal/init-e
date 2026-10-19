import InitECandidate.Runtime.HtrRequestRecordsMemory
import InitECandidate.Runtime.HtrRequestRecordsGlobals
import InitECandidate.Runtime.HtrRequestListBranchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def RequestRecordFrameContract (function : MlS) (ticks : Nat) : Prop :=
  ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64))
    (sha accelerator zeroHashes input heap out watched : BitVec 64),
    HashMemoryLayout state sha accelerator zeroHashes heap out watched →
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word input),.val (.word out)] → ticks ≤ state.clock →
    evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,post) →
    post.memory watched = state.memory watched ∧ post.globals = state.globals

theorem requestRecordFrameContract_deposit : RequestRecordFrameContract (ofString "htr_deposit") (htrDepositBodyCost + 1) := by
  intro F state post arguments sha accelerator zeroHashes input heap out watched layout args budget run
  exact ⟨htrDeposit_call_normal_memory state post arguments sha accelerator zeroHashes input heap out watched layout args budget run,
    htrDeposit_call_normal_globals state post arguments input out heap args layout.atHeap layout.code run⟩

theorem requestRecordFrameContract_wdreq : RequestRecordFrameContract (ofString "htr_wdreq") (htrWdreqBodyCost + 1) := by
  intro F state post arguments sha accelerator zeroHashes input heap out watched layout args budget run
  exact ⟨htrWdreq_call_normal_memory state post arguments sha accelerator zeroHashes input heap out watched layout args budget run,
    htrWdreq_call_normal_globals state post arguments input out heap args layout.atHeap layout.code run⟩

theorem requestRecordFrameContract_cons : RequestRecordFrameContract (ofString "htr_cons") (htrConsBodyCost + 1) := by
  intro F state post arguments sha accelerator zeroHashes input heap out watched layout args budget run
  exact ⟨htrCons_call_normal_memory state post arguments sha accelerator zeroHashes input heap out watched layout args budget run,
    htrCons_call_normal_globals state post arguments input out heap args layout.atHeap layout.code run⟩

theorem requestRecordFrameContract_bdep : RequestRecordFrameContract (ofString "htr_bdep") (htrBdepBodyCost + 1) := by
  intro F state post arguments sha accelerator zeroHashes input heap out watched layout args budget run
  exact ⟨htrBdep_call_normal_memory state post arguments sha accelerator zeroHashes input heap out watched layout args budget run,
    htrBdep_call_normal_globals state post arguments input out heap args layout.atHeap layout.code run⟩

theorem requestRecordFrameContract_bexit : RequestRecordFrameContract (ofString "htr_bexit") (htrBexitBodyCost + 1) := by
  intro F state post arguments sha accelerator zeroHashes input heap out watched layout args budget run
  exact ⟨htrBexit_call_normal_memory state post arguments sha accelerator zeroHashes input heap out watched layout args budget run,
    htrBexit_call_normal_globals state post arguments input out heap args layout.atHeap layout.code run⟩

theorem htrRequestList_branch_normal_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind tag pointer index size roots heap sha accelerator zeroHashes watched : BitVec 64) (function : MlS) (ticks : Nat)
    (contract : RequestRecordFrameContract function ticks)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap (roots + index * (32#64)) watched)
    (atKind : state.locals.lookup (ofString "kind") = some (.val (.word kind)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atSize : state.locals.lookup (ofString "sz") = some (.val (.word size)))
    (atRoots : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (budget : ticks ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrRequestListBranch tag function) = (none,post)) :
    post.memory watched = state.memory watched ∧ post.globals = state.globals := by
  rw [htrRequestList_branch_evaluate state kind tag function atKind] at run
  by_cases same : kind = tag
  · rw [if_pos same] at run
    exact contract state post htrRequestListArguments sha accelerator zeroHashes (pointer + index * size) heap
      (roots + index * (32#64)) watched layout
      (htrRequestList_arguments state pointer index size roots atPointer atIndex atSize atRoots) budget run
  · rw [if_neg same] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact ⟨rfl,rfl⟩

#print axioms requestRecordFrameContract_deposit
#print axioms requestRecordFrameContract_wdreq
#print axioms requestRecordFrameContract_cons
#print axioms requestRecordFrameContract_bdep
#print axioms requestRecordFrameContract_bexit
#print axioms htrRequestList_branch_normal_frame
end InitECandidate.Runtime
