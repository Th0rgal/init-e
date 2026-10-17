import InitECandidate.Runtime.HashCall32
import InitECandidate.Runtime.HashCallWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hash_supported_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointerArgument lengthArgument : ExpHOL 64) (pointer keyLength : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [pointerArgument,lengthArgument] =
        some [.val (.word pointer),.val (.word keyLength)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (aligned : pointer.toNat % 8 = 0)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (words : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))) :
    ∃ value : BitVec 64, ∃ ready, ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧
      ready.globals = state.globals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ready.locals = state.locals ∧ ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_hash") [pointerArgument,lengthArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word value)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  rcases supported with rfl | rfl | rfl
  · have domain : ∀ offset ∈ ([0,8] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset) := by
      intro offset member
      apply words
      change offset < 20
      simp at member
      omega
    have tailDomain : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
        state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 16 + extra)) := by
      intro extra member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · simpa using bytes 16 (by decide)
      · simpa [BitVec.add_assoc] using bytes 17 (by decide)
      · simpa [BitVec.add_assoc] using bytes 18 (by decide)
      · simpa [BitVec.add_assoc] using bytes 19 (by decide)
    exact evaluate_hash20_declaration state pointerArgument lengthArgument pointer arguments code clock aligned domain tailDomain
  · have domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset) := by
      intro offset member
      apply words
      change offset < 32
      simp at member
      omega
    exact evaluate_hash32_declaration state pointerArgument lengthArgument pointer arguments code clock aligned domain
  · have domain : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset) := by
      intro offset member
      apply words
      change offset < 52
      simp at member
      omega
    have tailDomain : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
        state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 48 + extra)) := by
      intro extra member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · simpa using bytes 48 (by decide)
      · simpa [BitVec.add_assoc] using bytes 49 (by decide)
      · simpa [BitVec.add_assoc] using bytes 50 (by decide)
      · simpa [BitVec.add_assoc] using bytes 51 (by decide)
    exact evaluate_hash52_declaration state pointerArgument lengthArgument pointer arguments code clock aligned domain tailDomain

#print axioms evaluate_hash_supported_declaration
end InitECandidate.Runtime
