import InitECandidate.Runtime.KeccakPaddedTailBound
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.MemzeroCallBound
import InitECandidate.Runtime.MemcpyCallBound
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_keccak_general_copy_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source index remainder output : BitVec 64)
    (atStp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atP : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (atI : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atRem : state.locals.lookup (ofString "rem") = some (.val (.word remainder)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (small : remainder.toNat < 136) (outAligned : output.toNat % 8 = 0)
    (code : state.code = originalRuntimeCode) (budget : 50 ≤ state.clock) :
    RunBounded state keccakAfterPadZero 50 := by
  let arguments : List (ExpHOL 64) := [.var .global (ofString "keccak_pad"),
    .op .add [.var .local (ofString "p"),.var .local (ofString "i")],.var .local (ofString "rem")]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pad),.val (.word (source + index)),.val (.word remainder)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [arguments,evalListHOLExact,evalHOLExact,atPad,atP,atI,atRem,wordOpHOL,wordOp,valueIsWord,valueWord]
  have first : RunBounded state (.call (some (none,none)) (ofString "memcpy") arguments) 31 :=
    (show RunBounded state (.call (some (none,none)) (ofString "memcpy") arguments)
      (remainder.toNat / 32 + remainder.toNat / 8 + 11) from
      evaluate_memcpy_call_bounded state arguments pad (source + index) remainder args code (by omega) (by omega)).weaken (by omega)
  rw [source_keccak_copy_prefix]
  change RunBounded state (.seq (.call (some (none,none)) (ofString "memcpy") arguments) keccakAfterCopy) (31 + 19)
  refine RunBounded.seq first budget ?_
  intro next normal nextCode remaining
  have locals := evaluate_discard_call_success_locals state (ofString "memcpy") arguments (by rw [normal])
  have globals := memcpy_call_globals_frame arguments state code
  rw [normal] at locals globals
  obtain ⟨result,post,run,spent,kept,safe⟩ := evaluate_keccak_padded_tail_bounded next pointer pad output
    (by rw [locals]; exact atStp) (by rw [globals]; exact atPad) (by rw [locals]; exact atOut)
    outAligned (nextCode.trans code) remaining
  unfold RunBounded
  rw [run]
  exact ⟨spent,kept,safe⟩

/-- The remainder path accepts any source alignment and needs no successful
memory-access premise. Faults in zeroing, copy, padding and FFI are bounded too. -/
theorem runBounded_keccak_general_remainder {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source index remainder output : BitVec 64)
    (atStp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atP : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (atI : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atRem : state.locals.lookup (ofString "rem") = some (.val (.word remainder)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (small : remainder.toNat < 136) (outAligned : output.toNat % 8 = 0)
    (code : state.code = originalRuntimeCode) (budget : 82 ≤ state.clock) :
    RunBounded state keccakRemainderTail 82 := by
  let arguments : List (ExpHOL 64) := [.var .global (ofString "keccak_pad"),.const 136]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pad),.val (.word (136#64))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [arguments,evalListHOLExact,evalHOLExact,atPad]
  have first : RunBounded state (.call (some (none,none)) (ofString "memzero") arguments) 32 :=
    evaluate_memzero_call_bounded state arguments pad (136#64) args code (by decide) (by change 32 ≤ state.clock; omega)
  rw [source_keccak_pad_zero_prefix]
  change RunBounded state (.seq (.call (some (none,none)) (ofString "memzero") arguments) keccakAfterPadZero) (32 + 50)
  refine RunBounded.seq first budget ?_
  intro next normal nextCode remaining
  have locals := evaluate_discard_call_success_locals state (ofString "memzero") arguments (by rw [normal])
  have globals := memzero_call_globals_frame arguments state code
  rw [normal] at locals globals
  exact runBounded_keccak_general_copy_tail next pointer pad source index remainder output
    (by rw [locals]; exact atStp) (by rw [globals]; exact atPad) (by rw [locals]; exact atP)
    (by rw [locals]; exact atI) (by rw [locals]; exact atRem) (by rw [locals]; exact atOut)
    small outAligned (nextCode.trans code) remaining

#print axioms runBounded_keccak_general_copy_tail
#print axioms runBounded_keccak_general_remainder
end InitECandidate.Runtime
