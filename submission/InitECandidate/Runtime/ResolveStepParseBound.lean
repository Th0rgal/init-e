import InitECandidate.Runtime.ResolveStepSource
import InitECandidate.Runtime.OriginalRlpItemCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.MptFailCallBound
import InitECandidate.Runtime.RlpItemBodyBound
import InitECandidate.Runtime.PanHandledCallBound
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def resolveStepParseCost (length : Nat) : Nat := length * ((2 * length + 1) * 15 + 19) + 92634

/-- The original handled parse call is bounded in all outcomes, including
parser exceptions and execution of the real one-tick MPT failure handler. -/
theorem runBounded_resolve_step_parse_call {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : resolveStepParseCost length.toNat ≤ s.clock) :
    RunBounded s resolveStepParseCall (resolveStepParseCost length.toNat) := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),.var .local (ofString "n")] =
      some [.val (.word pointer),.val (.word length)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atPointer,atLength]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item)
    (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_rlpItem_body_bounded entry pointer length scratch frame ceiling inputLimit p n
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change _ ≤ s.clock - 1; unfold resolveStepParseCost at budget; omega)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item) with
  | mk result bodyPost =>
    rw [bodyRun] at bounded
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
    rw [bodyRun] at metadata
    have spent : s.clock ≤ bodyPost.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633) := by
      have h := bounded.1
      change s.clock - 1 ≤ bodyPost.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632) at h
      unfold resolveStepParseCost at budget
      omega
    have remaining : bodyPost.clock ≤ s.clock := by
      have h := bounded.2.1
      change bodyPost.clock ≤ s.clock - 1 at h
      omega
    have handlerTicks : 0 < bodyPost.clock := by unfold resolveStepParseCost at budget; omega
    have composed := evaluate_handled_call_bounded s bodyPost (ofString "rlp_item") (ofString "RlpErr")
      (ofString "e") (some (.local,ofString "it")) _ _ (sourceFunctionBody Guest.guestFn_rlp_item)
      (.call (some (none,none)) (ofString "mpt_fail") [.const 3]) callee (.comb [.one,.one,.one,.one]) result
      (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633) 1 args lookup
      (by unfold resolveStepParseCost at budget; omega) bodyRun spent remaining bounded.2.2
      (by
        intro value exception
        have fail := evaluate_mptFail_call_bounded
          (setVarHOLFinite (ofString "e") value {bodyPost with locals := s.locals}) (.const 3) 3
          (metadata.1.trans code) (by change bodyPost.clock ≠ 0; omega)
          (by rw [evalListHOLFinite_eq_toExact]; rfl)
        exact ⟨by have h := fail.1; change _ = bodyPost.clock - 1 at h; omega,
          by have h := fail.1; change _ = bodyPost.clock - 1 at h; omega,fail.2.1⟩)
    rw [source_resolve_step_parse_call]
    exact composed

#print axioms runBounded_resolve_step_parse_call
end InitECandidate.Runtime
