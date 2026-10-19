import InitECandidate.Runtime.HtrRequestsBodyBound
import InitECandidate.Runtime.OriginalHtrRequestsCode
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrRequests_installed {F : Type} (state : PanSemStateFiniteExact 64 F) (record out : BitVec 64)
    (code : state.code = originalRuntimeCode) :
    lookupCodeHOLFinite state.code.lookup (ofString "htr_requests") [.val (.word record),.val (.word out)] =
      some (sourceFunctionBody Guest.guestFn_htr_requests,
        (HolFiniteMapExact.empty.update (ofString "rq",.val (.word record))).update (ofString "out",.val (.word out)),.one) :=
  pan_two_word_lookup state.code.lookup (ofString "htr_requests") (ofString "rq") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_requests) record out (by decide) (by rw [code]; exact originalRuntimeCode_htrRequests_lookup)

/-- The complete original five-list request-container call has one finite bound,
from decoded counts and workspace layout; the actual allocator may reject. -/
theorem runBounded_htrRequests_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (sha accelerator zeroHashes chunk record heap out : BitVec 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (decoded : HtrRequestsDecoded state record)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word record),.val (.word out)])
    (budget : htrRequestsBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_requests") arguments) (htrRequestsBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [htrRequests_installed state record out workspace.code] at lookup
  cases lookup
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "rq",.val (.word record))).update (ofString "out",.val (.word out)))
  have entryDecoded : HtrRequestsDecoded entry record := by
    intro index inside
    obtain ⟨pointer,count,old,small⟩ := decoded index inside
    exact ⟨pointer,count,old.after_frame state entry record index pointer count rfl rfl rfl,small⟩
  have ctx : HtrRequestsEntryContext entry sha accelerator zeroHashes chunk record heap out := {
    toHtrRequestsWorkspace := workspace.transfer rfl rfl
    atRecord := by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    atOut := by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    decoded := entryDecoded }
  exact runBounded_htrRequests_body entry sha accelerator zeroHashes chunk record heap out ctx
    (by change htrRequestsBodyCost ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget)

#print axioms htrRequests_installed
#print axioms runBounded_htrRequests_call
end InitECandidate.Runtime
