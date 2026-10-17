import InitECandidate.Runtime.CompactNibbleBufferBody
import InitECandidate.Runtime.CompactNibbleEmptyBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Uniform full-body contract including the empty-input error path. The
returned path is valid and bounded whenever the decoder returns a value. -/
theorem evaluate_compactNibble_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out : BitVec 64)
    (lengthBound : 2 * length.toNat + 8 < 2^64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (sourceDomain : ∀ offset : Nat, offset < length.toNat →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * length.toNat →
      state.memaddrs (panByteAlignHOL (out + BitVec.ofNat 64 offset)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word out)))
    (request : 2 * length ≤ (33806089496 : BitVec 64) - out)
    (finishBound : (allocationEnd out (2 * length)).toNat ≤ 33806089496)
    (ticks : length.toNat / 4 + 5 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_compact_to_nibbles) = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat / 4 + 5) ∧ post.clock ≤ state.clock ∧
      result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ count leaf : BitVec 64,
        value = .rStruct [.val (.word out),.val (.word count),.val (.word leaf)] ∧
        count.toNat ≤ 2 * length.toNat ∧ leaf.toNat ≤ 1 ∧ TrieNibbleRange post out count) := by
  by_cases zero : length = 0
  · subst length
    have empty := evaluate_compactNibble_empty_body state lengthLocal code (by omega)
    generalize run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_compact_to_nibbles) = evaluated at empty
    obtain ⟨result,post⟩ := evaluated
    obtain ⟨clock,noTimeout,_,noReturn⟩ := empty
    dsimp only at clock noTimeout noReturn
    refine ⟨result,post,rfl,by omega,by omega,noTimeout,?_⟩
    intro value returned
    exact False.elim (noReturn value returned)
  · have smaller : (length - 1).toNat ≤ length.toNat := by
      have positive : 0 < length.toNat := by
        by_contra h
        apply zero
        apply BitVec.eq_of_toNat_eq
        simpa using (show length.toNat = 0 by omega)
      rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 1 ≤ length.toNat; omega)]
      omega
    have budget : (length - 1).toNat / 4 + 5 ≤ length.toNat / 4 + 5 := by
      have divided : (length - 1).toNat / 4 ≤ length.toNat / 4 := Nat.div_le_div_right smaller
      omega
    obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ :=
      evaluate_compactNibble_buffer_body state pointer length out zero lengthBound pointerLocal lengthLocal code
        sourceDomain outputDomain heapGlobal request finishBound (by omega)
    exact ⟨result,post,run,by omega,remaining,noTimeout,returned⟩

#print axioms evaluate_compactNibble_body_bounded
end InitECandidate.Runtime
