import InitECandidate.Runtime.MptHashScratchGlobalKeep
import InitECandidate.Runtime.RunAttemptHeadersEntry
import InitECandidate.Runtime.RunAttemptHeadersDeclarationContract
/-!
The caller keeps `mpt_hash_scratch` across the real validation call.

`validate_headers_keeps_mpt_hash_scratch` gives the workspace global at the end
of the returned validating body; a declaration call restores the caller's
local scope and carries the body's globals forward, so the same value is available in the
declaration's reached state.  Both transfers below consume the retained returned
body run rather than assuming any call frame.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 600000

/-- The returned validating body leaves the caller's `mpt_hash_scratch` value
unchanged. -/
theorem run_attempt_headers_body_keeps_mpt_hash_scratch {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (array count : BitVec 64) (value : ValueHOL 64)
    (code : (callEntryStateHOLFinite s (validateHeadersCallee array count)).code = originalRuntimeCode)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite s (validateHeadersCallee array count))
      (sourceFunctionBody Guest.guestFn_validate_headers) = (some (.returned value),post)) :
    post.globals.lookup (ofString "mpt_hash_scratch") = s.globals.lookup (ofString "mpt_hash_scratch") := by
  have kept := validate_headers_keeps_mpt_hash_scratch
    (callEntryStateHOLFinite s (validateHeadersCallee array count)) code
  rw [run] at kept
  exact kept

/-- The actual `run_attempt` declaration reaches its continuation with the
caller's `mpt_hash_scratch` value retained. -/
theorem run_attempt_headers_declaration_keeps_mpt_hash_scratch {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (si array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling inputLimit : Nat)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling)
    (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 72 80 array count input inputLength heap)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 →
      s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (budget : validateHeadersBodyCost inputLimit + 1 ≤ s.clock) :
    Reaches s (runAttemptAt 2)
      (fun ready => ∃ value : ValueHOL 64, ∃ bodyPost : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState (callEntryStateHOLFinite s (validateHeadersCallee array count))
          (sourceFunctionBody Guest.guestFn_validate_headers) = (some (.returned value),bodyPost) ∧
        ready.globals = bodyPost.globals ∧ ready.code = s.code ∧
        ready.globals.lookup (ofString "mpt_hash_scratch") = s.globals.lookup (ofString "mpt_hash_scratch"))
      (validateHeadersBodyCost inputLimit + 1) (runAttemptAt 3) := by
  have reached := run_attempt_headers_declaration_reaches s si array count input inputLength scratch frame heap
    keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove inputBefore orderedFrame
    framePositive scratchBelow ceilingAligned stateBelow padBelow atSi linked scratchGlobal frameGlobal
    stateGlobal padGlobal arena heapArena heapGlobal heapBound code budget
  refine reaches_mono s (runAttemptAt 2) (runAttemptAt 3) _ _ _ _ (le_refl _) ?_ reached
  intro ready facts
  obtain ⟨value,bodyPost,bodyRun,pinLocal,memoryEq,globalsEq,domainEq,codeEq⟩ := facts
  have bodyKept := run_attempt_headers_body_keeps_mpt_hash_scratch s bodyPost array count value code bodyRun
  exact ⟨value,bodyPost,bodyRun,globalsEq,codeEq,(by rw [globalsEq]; exact bodyKept)⟩

#print axioms run_attempt_headers_body_keeps_mpt_hash_scratch
#print axioms run_attempt_headers_declaration_keeps_mpt_hash_scratch
end InitECandidate.Runtime
