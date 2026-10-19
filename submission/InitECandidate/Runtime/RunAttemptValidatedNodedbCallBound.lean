import InitECandidate.Runtime.RunAttemptDatabaseContext
import InitECandidate.Runtime.RunAttemptNodedbCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- At the actual database site, validation's retained contract supplies the
live aligned heap, workspace pointers and preserved state-witness list.
Only the hash-output workspace pointer is still supplied separately. -/
theorem runBounded_run_attempt_validated_nodedb_call {F : Type}
    (before ready : PanSemStateFiniteExact 64 F)
    (si headers headerCount input inputLength scratch frame heap keccakState keccakPad parent : BitVec 64)
    (ceiling : Nat)
    (facts : RunAttemptHeaderValidationFacts before ready si headers headerCount input inputLength
      scratch frame heap keccakState keccakPad ceiling)
    (array total output : BitVec 64) (destination : Option (VarKind × MlS))
    (linked : WitnessArrayLinked before si 40 48 array total input inputLength heap)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (arrayAbove : total.toNat = 0 ∨ ceiling ≤ array.toNat)
    (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling) (outputAligned : output.toNat % 8 = 0)
    (atOutput : ready.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (inputSmall : inputLength.toNat ≤ 134217712) (code : before.code = originalRuntimeCode)
    (budget : nodedbBodyCost total + 1 ≤ ready.clock) :
    RunBounded
      (runAttemptDatabaseState ready headerCount parent (allocationEnd heap (validateHeadersHsSize headerCount)))
      (.call (some (destination,none)) (ofString "nodedb_build") runAttemptNodedbArguments)
      (nodedbBodyCost total + 1) := by
  obtain ⟨finalHeap,atHeap,monotone,bounded,aligned,witness,arena⟩ :=
    facts.keeps_witness_array before ready si headers headerCount input inputLength scratch frame heap
      keccakState keccakPad ceiling 40 48 array total linked (by decide) (by decide)
      recordAbove recordBefore arrayAbove
  obtain ⟨atSi,atParent,atCount,atHashes,atHashesCount,atScratch,atFrame,atState,atPad,codeEq,domainEq,contextHeap⟩ :=
    facts.database_context before ready si headers headerCount input inputLength scratch frame heap
      keccakState keccakPad parent ceiling
  have nextWitness := witness.after_run_attempt_database_prefix ready si 40 48 array total input inputLength
    finalHeap headerCount parent (allocationEnd heap (validateHeadersHsSize headerCount))
  apply runBounded_run_attempt_nodedb_call _ si finalHeap total array input inputLength keccakState keccakPad output
    destination atSi nextWitness (codeEq.trans code) _ aligned bounded atState atPad _ inputSmall outputAligned _ _ budget
  · simpa (config := {decide := true}) [runAttemptDatabaseState,setGlobalHOLFinite,setVarHOLFinite,FUPDATE] using atHeap
  · simpa (config := {decide := true}) [runAttemptDatabaseState,setGlobalHOLFinite,setVarHOLFinite,FUPDATE] using atOutput
  · intro nonempty
    rcases arrayAbove with empty | above
    · exact (nonempty (BitVec.eq_of_toNat_eq empty)).elim
    · exact ⟨by omega,by omega,by omega⟩
  · intro address _ lo hi
    exact arena address lo hi

#print axioms runBounded_run_attempt_validated_nodedb_call
end InitECandidate.Runtime
