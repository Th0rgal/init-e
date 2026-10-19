import InitECandidate.Runtime.ValidateHeadersHashCallBound
import InitECandidate.Runtime.KeccakFullCallWindow
import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.RlpSliceInputPrefixBetween
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- A successful actual validation hash call keeps the witness array and
caller locals/globals. Its three write windows are explicit geometric obligations. -/
theorem validate_headers_hash_normal_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count index pointer length input inputLength hashes keccakState keccakPad upper : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes)))
    (inside : index.toNat < count.toNat)
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (above : ceiling ≤ array.toNat) (before : array.toNat + count.toNat * 16 ≤ upper.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit ≤ 134217712)
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (code : s.code = originalRuntimeCode) (budget : inputLimit * 20 + 125 ≤ s.clock)
    (outsideState : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < upper.toNat → ¬ MWin keccakState 200 address)
    (outsidePad : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < upper.toNat → ¬ MWin keccakPad 136 address)
    (outsideOutput : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < upper.toNat → ¬ MWin (hashes + index * 32) 32 address)
    (run : evaluateHOLFiniteState s validateHeadersHashCall = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
      post.locals = s.locals ∧ post.globals = s.globals ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < upper.toNat → post.memory address = s.memory address) := by
  have lengthBound := (entry.length_bound s array index pointer length input inputLength).trans inputBound
  have args := eval_validate_headers_hash_arguments s array index pointer length input inputLength hashes atArray atIndex atHashes entry
  have memory : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < upper.toNat → post.memory address = s.memory address := by
    intro address lo hi
    have kept := keccak_full_call_window s keccakState keccakPad pointer length (hashes + index * 32) address validateHeadersHashArguments
      stateGlobal padGlobal args (by omega) code (by omega) (outsideState address lo hi) (outsidePad address lo hi) (outsideOutput address lo hi)
    change (evaluateHOLFiniteState s validateHeadersHashCall).2.memory address = _ ∧ _ at kept
    rw [run] at kept
    exact kept.1
  have globals := keccak_full_call_window s keccakState keccakPad pointer length (hashes + index * 32) array validateHeadersHashArguments
    stateGlobal padGlobal args (by omega) code (by omega) (outsideState array above (by omega))
    (outsidePad array above (by omega)) (outsideOutput array above (by omega))
  change (evaluateHOLFiniteState s validateHeadersHashCall).2.memory array = _ ∧
    (evaluateHOLFiniteState s validateHeadersHashCall).2.globals = s.globals at globals
  rw [run] at globals
  have locals := evaluate_discard_call_success_locals s (ofString "keccak256") validateHeadersHashArguments
    (by change (evaluateHOLFiniteState s validateHeadersHashCall).1 = none; rw [run])
  change (evaluateHOLFiniteState s validateHeadersHashCall).2.locals = _ at locals
  rw [run] at locals
  have metadata := evaluateHOLFiniteState_metadata s validateHeadersHashCall
  rw [run] at metadata
  exact ⟨table.after_memory_between s post array count input inputLength upper ceiling above before metadata.2.1
      (fun address hi lo => memory address lo hi),locals,globals.2,metadata.2.1,metadata.1,memory⟩

#print axioms validate_headers_hash_normal_frame
end InitECandidate.Runtime
