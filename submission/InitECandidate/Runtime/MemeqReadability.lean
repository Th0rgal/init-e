import InitECandidate.Runtime.MemeqFastPaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem eval_memeqAddress {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer : BitVec 64) (offset : Nat)
    (binding : state.locals.lookup name = some (.val (.word pointer))) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (memeqAddress name offset) = some (.val (.word (pointer + BitVec.ofNat 64 offset))) := by
  by_cases zero : offset = 0
  · subst offset
    simpa [memeqAddress,evalHOLExact] using binding
  · simp [memeqAddress,zero,evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord]

theorem eval_memeqWord_readable {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer : BitVec 64) (offset : Nat)
    (binding : state.locals.lookup name = some (.val (.word pointer)))
    (domain : state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    ∃ value : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (memeqAddress name offset)) = some (.val (.word value)) := by
  obtain ⟨value,cell⟩ : ∃ value : BitVec 64, state.memory (pointer + BitVec.ofNat 64 offset) = .word value := by
    cases state.memory (pointer + BitVec.ofNat 64 offset) with | word value => exact ⟨value,rfl⟩
  refine ⟨value,?_⟩
  simp only [evalHOLExact,isWfShapeExactHOL]
  rw [eval_memeqAddress state name pointer offset binding]
  simp [memLoadHOLExact,domain,cell]

theorem eval_memeqByte_readable {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer : BitVec 64) (offset : Nat)
    (binding : state.locals.lookup name = some (.val (.word pointer)))
    (domain : state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))) :
    ∃ value : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (memeqAddress name offset)) = some (.val (.word value)) := by
  obtain ⟨value,cell⟩ : ∃ value : BitVec 64,
      state.memory (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)) = .word value := by
    cases state.memory (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)) with | word value => exact ⟨value,rfl⟩
  refine ⟨BitVec.ofNat 64 (panGetByteHOL (pointer + BitVec.ofNat 64 offset) value state.be).toNat,?_⟩
  rw [evalHOLExact,eval_memeqAddress state name pointer offset binding]
  simp [panMemLoadByteHOL,domain,cell]

/-- Domain membership for the listed word and byte offsets suffices to run
an entire mixed comparison chain without any source-clock cost. -/
theorem evaluate_memeq_offsets {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (words bytes : List Nat)
    (aLocal : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (wordDomain : ∀ offset ∈ words, state.memaddrs (a + BitVec.ofNat 64 offset) ∧
      state.memaddrs (b + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset ∈ bytes, state.memaddrs (panByteAlignHOL (a + BitVec.ofNat 64 offset)) ∧
      state.memaddrs (panByteAlignHOL (b + BitVec.ofNat 64 offset))) :
    ∃ value : BitVec 64, (value = 0 ∨ value = 1) ∧
      evaluateHOLFiniteState state (memeqChecks (words.map memeqWordPair ++ bytes.map memeqBytePair)) =
        (some (.returned (.val (.word value))),emptyLocalsHOLFinite state) := by
  apply evaluate_memeqChecks
  intro pair member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨offset,inside,rfl⟩ := List.mem_map.mp member
    obtain ⟨left,l⟩ := eval_memeqWord_readable state (ofString "a") a offset aLocal (wordDomain offset inside).1
    obtain ⟨right,r⟩ := eval_memeqWord_readable state (ofString "b") b offset bLocal (wordDomain offset inside).2
    exact ⟨left,right,l,r⟩
  · obtain ⟨offset,inside,rfl⟩ := List.mem_map.mp member
    obtain ⟨left,l⟩ := eval_memeqByte_readable state (ofString "a") a offset aLocal (byteDomain offset inside).1
    obtain ⟨right,r⟩ := eval_memeqByte_readable state (ofString "b") b offset bLocal (byteDomain offset inside).2
    exact ⟨left,right,l,r⟩

#print axioms evaluate_memeq_offsets
#print axioms eval_memeqAddress
#print axioms eval_memeqWord_readable
#print axioms eval_memeqByte_readable
end InitECandidate.Runtime
