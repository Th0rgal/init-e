import InitECandidate.Runtime.RunAttemptDatabaseContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both original database witnesses survive header validation and the exact
caller prefix at one execution-derived allocation frontier. -/
theorem RunAttemptHeaderValidationFacts.database_witnesses {F : Type}
    (s ready : PanSemStateFiniteExact 64 F)
    (si headers headerCount input inputLength scratch frame heap keccakState keccakPad parent : BitVec 64)
    (ceiling : Nat)
    (facts : RunAttemptHeaderValidationFacts s ready si headers headerCount input inputLength
      scratch frame heap keccakState keccakPad ceiling)
    (nodeArray nodeCount codeArray codeCount : BitVec 64)
    (nodes : WitnessArrayLinked s si 40 48 nodeArray nodeCount input inputLength heap)
    (codes : WitnessArrayLinked s si 56 64 codeArray codeCount input inputLength heap)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (nodesAbove : nodeCount.toNat = 0 ∨ ceiling ≤ nodeArray.toNat)
    (codesAbove : codeCount.toNat = 0 ∨ ceiling ≤ codeArray.toNat) :
    let next := runAttemptDatabaseState ready headerCount parent
      (allocationEnd heap (validateHeadersHsSize headerCount))
    ∃ finalHeap : BitVec 64,
      next.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧
      WitnessArrayLinked next si 40 48 nodeArray nodeCount input inputLength finalHeap ∧
      WitnessArrayLinked next si 56 64 codeArray codeCount input inputLength finalHeap ∧
      (∀ address : BitVec 64, finalHeap.toNat ≤ address.toNat → address.toNat < 33806089496 →
        next.memaddrs address) := by
  obtain ⟨nodeHeap,nodeAt,nodeMono,nodeBound,nodeAligned,nodeLinked,nodeArena⟩ :=
    facts.keeps_witness_array s ready si headers headerCount input inputLength scratch frame heap
      keccakState keccakPad ceiling 40 48 nodeArray nodeCount nodes (by decide) (by decide)
      recordAbove recordBefore nodesAbove
  obtain ⟨codeHeap,codeAt,codeMono,codeBound,codeAligned,codeLinked,codeArena⟩ :=
    facts.keeps_witness_array s ready si headers headerCount input inputLength scratch frame heap
      keccakState keccakPad ceiling 56 64 codeArray codeCount codes (by decide) (by decide)
      recordAbove recordBefore codesAbove
  have same : codeHeap = nodeHeap := by
    rw [nodeAt] at codeAt
    cases codeAt
    rfl
  subst codeHeap
  dsimp only
  refine ⟨nodeHeap,?_,nodeMono,nodeBound,nodeAligned,?_,?_,nodeArena⟩
  · simpa (config := {decide := true}) [runAttemptDatabaseState,setGlobalHOLFinite,setVarHOLFinite,FUPDATE] using nodeAt
  · exact nodeLinked.after_run_attempt_database_prefix ready si 40 48 nodeArray nodeCount input inputLength
      nodeHeap headerCount parent (allocationEnd heap (validateHeadersHsSize headerCount))
  · exact codeLinked.after_run_attempt_database_prefix ready si 56 64 codeArray codeCount input inputLength
      nodeHeap headerCount parent (allocationEnd heap (validateHeadersHsSize headerCount))

#print axioms RunAttemptHeaderValidationFacts.database_witnesses
end InitECandidate.Runtime
