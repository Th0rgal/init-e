import InitECandidate.Runtime.HashPartialSyntax
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem eval_hashLoadLE32_readable {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (offset : Nat)
    (binding : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (domain : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset + extra))) :
    ∃ value : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (hashLoadLE32 offset) = some (.val (.word value)) := by
  have d0 := domain 0 (by simp)
  have d1 := domain 1 (by simp)
  have d2 := domain 2 (by simp)
  have d3 := domain 3 (by simp)
  obtain ⟨v0,c0⟩ : ∃ v : BitVec 64, state.memory
      (panByteAlignHOL (pointer + BitVec.ofNat 64 offset + 0)) = .word v := by
    cases state.memory (panByteAlignHOL (pointer + BitVec.ofNat 64 offset + 0)) with
    | word v => exact ⟨v,rfl⟩
  obtain ⟨v1,c1⟩ : ∃ v : BitVec 64, state.memory
      (panByteAlignHOL (pointer + BitVec.ofNat 64 offset + 1)) = .word v := by
    cases state.memory (panByteAlignHOL (pointer + BitVec.ofNat 64 offset + 1)) with
    | word v => exact ⟨v,rfl⟩
  obtain ⟨v2,c2⟩ : ∃ v : BitVec 64, state.memory
      (panByteAlignHOL (pointer + BitVec.ofNat 64 offset + 2)) = .word v := by
    cases state.memory (panByteAlignHOL (pointer + BitVec.ofNat 64 offset + 2)) with
    | word v => exact ⟨v,rfl⟩
  obtain ⟨v3,c3⟩ : ∃ v : BitVec 64, state.memory
      (panByteAlignHOL (pointer + BitVec.ofNat 64 offset + 3)) = .word v := by
    cases state.memory (panByteAlignHOL (pointer + BitVec.ofNat 64 offset + 3)) with
    | word v => exact ⟨v,rfl⟩
  simp at d0 c0
  simp only [BitVec.add_assoc] at d1 d2 d3 c1 c2 c3
  unfold hashLoadLE32
  rw [evalHOLExact,evalListHOLExact,evalHOLExact,
    eval_memeqAddress state (ofString "p") pointer offset binding]
  simp [evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord,
    panMemLoadByteHOL,d0,c0,wordShiftHOL]
  simp_all [BitVec.add_assoc]

#print axioms eval_hashLoadLE32_readable
end InitECandidate.Runtime
