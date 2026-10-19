import InitECandidate.Runtime.RunAttemptValidatedWitness
import InitECandidate.Runtime.MptHashScratchCallerKeep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def runAttemptDatabaseState {F : Type} (ready : PanSemStateFiniteExact 64 F)
    (count parent hashes : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
    (setGlobalHOLFinite (ofString "block_hashes") (.val (.word hashes))
      (setVarHOLFinite (ofString "parent") (.val (.word parent))
        (setVarHOLFinite (ofString "nh") (.val (.word count)) ready)))

/-- The exact caller prefix retains validation's live allocation arena and
workspace pointers, and exposes the typed locals used by database setup. -/
theorem RunAttemptHeaderValidationFacts.database_context {F : Type}
    (s ready : PanSemStateFiniteExact 64 F)
    (si headers count input inputLength scratch frame heap keccakState keccakPad parent : BitVec 64)
    (ceiling : Nat)
    (facts : RunAttemptHeaderValidationFacts s ready si headers count input inputLength
      scratch frame heap keccakState keccakPad ceiling) :
    let next := runAttemptDatabaseState ready count parent (allocationEnd heap (validateHeadersHsSize count))
    next.locals.lookup (ofString "si") = some (.val (.word si)) ∧
    next.locals.lookup (ofString "parent") = some (.val (.word parent)) ∧
    next.locals.lookup (ofString "nh") = some (.val (.word count)) ∧
    next.globals.lookup (ofString "block_hashes") =
      some (.val (.word (allocationEnd heap (validateHeadersHsSize count)))) ∧
    next.globals.lookup (ofString "block_hashes_n") = some (.val (.word count)) ∧
    next.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
    next.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
    next.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)) ∧
    next.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)) ∧
    next.code = s.code ∧ next.memaddrs = s.memaddrs ∧
    ∃ finalHeap : BitVec 64,
      next.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧
      (∀ address : BitVec 64, finalHeap.toNat ≤ address.toNat → address.toNat < 33806089496 →
        next.memaddrs address) := by
  obtain ⟨value,bodyPost,bodyRun,locals,memoryEq,globalsEq,domainEq,codeEq,valueIs,vhLocal,cap,
    ⟨finalHeap,atHeap,monotone,bounded,aligned,bodyArena,arena⟩,
    scratchPost,framePost,statePost,padPost,window,tablePost,prefixReady,initialized,atSiReady⟩ := facts
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,codeEq,domainEq,finalHeap,?_,monotone,bounded,aligned,arena⟩
  all_goals simp (config := {decide := true})
    [runAttemptDatabaseState,setGlobalHOLFinite,setVarHOLFinite,FUPDATE,
      atSiReady,scratchPost,framePost,statePost,padPost,atHeap]

#print axioms RunAttemptHeaderValidationFacts.database_context

/-- The retained actual returned callee run supplies the missing database
hash-workspace global, without a post-call preservation assumption. -/
theorem RunAttemptHeaderValidationFacts.mpt_hash_scratch {F : Type}
    (s ready : PanSemStateFiniteExact 64 F)
    (si headers count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling : Nat)
    (facts : RunAttemptHeaderValidationFacts s ready si headers count input inputLength
      scratch frame heap keccakState keccakPad ceiling)
    (code : s.code = originalRuntimeCode) :
    ready.globals.lookup (ofString "mpt_hash_scratch") = s.globals.lookup (ofString "mpt_hash_scratch") := by
  obtain ⟨value,bodyPost,bodyRun,locals,memoryEq,globalsEq,rest⟩ := facts
  rw [globalsEq]
  exact run_attempt_headers_body_keeps_mpt_hash_scratch s bodyPost headers count value code bodyRun

#print axioms RunAttemptHeaderValidationFacts.mpt_hash_scratch
end InitECandidate.Runtime
