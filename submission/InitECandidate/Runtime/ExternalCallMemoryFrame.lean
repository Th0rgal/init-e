import InitECandidate.Runtime.WriteBytearrayMemoryFrame
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem evaluate_external_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64)
    (address1 length1 address2 length2 watched : BitVec 64)
    (h1 : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) configuration = some (.val (.word address1)))
    (h2 : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) configurationLength = some (.val (.word length1)))
    (h3 : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) array = some (.val (.word address2)))
    (h4 : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arrayLength = some (.val (.word length2)))
    (separate : ∀ offset : Nat, offset < length2.toNat → watched ≠ panByteAlignHOL (address2 + BitVec.ofNat 64 offset)) :
    (evaluateHOLFiniteState state (.extCall function configuration configurationLength array arrayLength)).2.memory watched =
      state.memory watched := by
  classical
  rw [evaluateHOLFiniteState_extCall_source,h1,h2,h3,h4]
  dsimp only
  cases first : readBytearrayWordHOL (byteWidth := 8) address1 length1.toNat
      (@panMemLoadByteWord8HOL 64 _ state.memory state.memaddrs (fun a => Classical.propDecidable (state.memaddrs a)) state.be) with
  | none => rfl
  | some bytes1 =>
    cases second : readBytearrayWordHOL (byteWidth := 8) address2 length2.toNat
        (@panMemLoadByteWord8HOL 64 _ state.memory state.memaddrs (fun a => Classical.propDecidable (state.memaddrs a)) state.be) with
    | none => rfl
    | some bytes2 =>
      dsimp only
      cases called : callFFIHOL state.ffi (.extCall function) bytes1 bytes2 with
      | final event => rfl
      | ret newFfi newBytes =>
        have inputLength := readBytearrayWordHOL_length address2 length2.toNat _ bytes2 second
        have returnedLength := callFFIHOL_ret_length state.ffi (.extCall function) bytes1 bytes2 newBytes newFfi called
        change panWriteBytearrayWord8HOL address2 newBytes state.memory state.memaddrs state.be watched = state.memory watched
        apply panWriteBytearray_memory_other
        intro offset inside
        exact separate offset (by omega)

/-- No output-domain or successful-FFI assumption: all failure and terminal
outcomes also preserve watched memory outside the aligned output interval. -/
theorem evaluate_external_interval_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64)
    (address1 length1 address2 length2 watched : BitVec 64)
    (h1 : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) configuration = some (.val (.word address1)))
    (h2 : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) configurationLength = some (.val (.word length1)))
    (h3 : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) array = some (.val (.word address2)))
    (h4 : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arrayLength = some (.val (.word length2)))
    (aligned : address2.toNat % 8 = 0) (fits : address2.toNat + length2.toNat ≤ 33806089496)
    (outside : watched.toNat < address2.toNat ∨ address2.toNat + length2.toNat ≤ watched.toNat) :
    (evaluateHOLFiniteState state (.extCall function configuration configurationLength array arrayLength)).2.memory watched =
      state.memory watched := by
  exact evaluate_external_memory_frame state function configuration configurationLength array arrayLength
    address1 length1 address2 length2 watched h1 h2 h3 h4
    (fun offset inside => (memcpy_interval_separate address2 length2 watched aligned fits outside offset inside).2)

#print axioms evaluate_external_memory_frame
#print axioms evaluate_external_interval_frame
end InitECandidate.Runtime
