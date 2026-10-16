import InitECandidate.Runtime.MemeqSelect32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memeqAfter52 : ProgHOL 64 :=
  match memeqAfter32 with | .seq _ rest => rest | _ => .skip

theorem source_memeq_after32 : memeqAfter32 =
    .seq (.ite (memeqSizeCondition 52) memeqFast52 .skip) memeqAfter52 := by rfl

theorem evaluate_memeq_aligned20 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64)
    (aLocal : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word (20 : BitVec 64))))
    (wordDomain : ∀ offset ∈ ([0,8] : List Nat),
      state.memaddrs (a + BitVec.ofNat 64 offset) ∧ state.memaddrs (b + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset ∈ ([16,17,18,19] : List Nat),
      state.memaddrs (panByteAlignHOL (a + BitVec.ofNat 64 offset)) ∧
      state.memaddrs (panByteAlignHOL (b + BitVec.ofNat 64 offset))) :
    ∃ value : BitVec 64, (value = 0 ∨ value = 1) ∧ evaluateHOLFiniteState state memeqAlignedBody =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite state) := by
  have flag20 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (memeqSizeCondition 20) =
        some (.val (.word (1 : BitVec 64))) := by
    simp [memeqSizeCondition,evalHOLExact,sizeLocal,Compiler.Encoders.Asm.wordCmpHOL]
  obtain ⟨value,boolean,run⟩ := evaluate_memeq_offsets state a b [0,8] [16,17,18,19] aLocal bLocal wordDomain byteDomain
  have fast : evaluateHOLFiniteState state memeqFast20 =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite state) := by
    rw [source_memeq_fast20]
    exact run
  refine ⟨value,boolean,?_⟩
  rw [source_memeq_aligned_prefix,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,flag20]
  simp only [show ¬(1 : BitVec 64) = 0 by decide,fast]
  rfl

theorem evaluate_memeq_aligned52 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64)
    (aLocal : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word (52 : BitVec 64))))
    (wordDomain : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat),
      state.memaddrs (a + BitVec.ofNat 64 offset) ∧ state.memaddrs (b + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset ∈ ([48,49,50,51] : List Nat),
      state.memaddrs (panByteAlignHOL (a + BitVec.ofNat 64 offset)) ∧
      state.memaddrs (panByteAlignHOL (b + BitVec.ofNat 64 offset))) :
    ∃ value : BitVec 64, (value = 0 ∨ value = 1) ∧ evaluateHOLFiniteState state memeqAlignedBody =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite state) := by
  have flag20 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (memeqSizeCondition 20) =
        some (.val (.word (0 : BitVec 64))) := by
    simp [memeqSizeCondition,evalHOLExact,sizeLocal,Compiler.Encoders.Asm.wordCmpHOL]
  have flag32 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (memeqSizeCondition 32) =
        some (.val (.word (0 : BitVec 64))) := by
    simp [memeqSizeCondition,evalHOLExact,sizeLocal,Compiler.Encoders.Asm.wordCmpHOL]
  have flag52 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (memeqSizeCondition 52) =
        some (.val (.word (1 : BitVec 64))) := by
    simp [memeqSizeCondition,evalHOLExact,sizeLocal,Compiler.Encoders.Asm.wordCmpHOL]
  obtain ⟨value,boolean,run⟩ := evaluate_memeq_offsets state a b [0,8,16,24,32,40] [48,49,50,51] aLocal bLocal wordDomain byteDomain
  have fast : evaluateHOLFiniteState state memeqFast52 =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite state) := by
    rw [source_memeq_fast52]
    exact run
  refine ⟨value,boolean,?_⟩
  rw [source_memeq_aligned_prefix,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,flag20]
  simp only [if_pos,evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,flag32]
  simp only [if_pos,evaluateHOLFiniteState_skip]
  rw [source_memeq_after32,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,flag52]
  simp only [show ¬(1 : BitVec 64) = 0 by decide,fast]
  rfl

#print axioms evaluate_memeq_aligned20
#print axioms evaluate_memeq_aligned52
end InitECandidate.Runtime
