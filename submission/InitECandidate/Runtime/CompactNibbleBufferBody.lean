import InitECandidate.Runtime.CompactNibbleNonemptyBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full nonempty decoder contract stated only with the input/output buffers
and allocator state. Header values and suffix domains are derived internally. -/
theorem evaluate_compactNibble_buffer_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out : BitVec 64)
    (nonzero : length ≠ 0)
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
    (ticks : (length - 1).toNat / 4 + 5 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_compact_to_nibbles) = (result,post) ∧
      state.clock ≤ post.clock + ((length - 1).toNat / 4 + 5) ∧ post.clock ≤ state.clock ∧
      result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ count leaf : BitVec 64,
        value = .rStruct [.val (.word out),.val (.word count),.val (.word leaf)] ∧
        count.toNat ≤ 2 * length.toNat ∧ leaf.toNat ≤ 1 ∧ TrieNibbleRange post out count) := by
  have positive : 0 < length.toNat := by
    by_contra h
    have zero : length = 0 := by apply BitVec.eq_of_toNat_eq; simpa using (show length.toNat = 0 by omega)
    exact nonzero zero
  have tailNat : (length - 1).toNat = length.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 1 ≤ length.toNat; omega)]
    rfl
  have headerDomain : state.memaddrs (panByteAlignHOL pointer) := by
    simpa using sourceDomain 0 positive
  obtain ⟨cell,cellRead⟩ : ∃ cell : BitVec 64, state.memory (panByteAlignHOL pointer) = .word cell := by
    cases state.memory (panByteAlignHOL pointer) with
    | word cell => exact ⟨cell,rfl⟩
  let byte := panGetByteHOL pointer cell state.be
  have loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte := by
    simp [panMemLoadByteHOL,headerDomain,cellRead,byte]
  let c0 := BitVec.ofNat 64 byte.toNat
  let first := c0 >>> (4 : Nat)
  let odd := first &&& 1
  let leaf := (first >>> (1 : Nat)) &&& 1
  let initial : BitVec 64 := if odd = 0 then 0 else 1
  have initialSmall : initial.toNat ≤ 1 := by
    dsimp only [initial]
    split <;> decide +kernel
  have leafSmall : leaf.toNat ≤ 1 := by
    dsimp only [leaf]
    rw [BitVec.toNat_and]
    exact Nat.and_le_right
  have suffixSource : ∀ offset : Nat, offset < (length - 1).toNat →
      state.memaddrs (panByteAlignHOL ((pointer + 1) + BitVec.ofNat 64 offset)) := by
    intro offset inside
    have access := sourceDomain (1 + offset) (by omega)
    simpa [BitVec.ofNat_add,BitVec.add_assoc] using access
  have suffixOutput : ∀ offset : Nat, offset < 2 * (length - 1).toNat →
      state.memaddrs (panByteAlignHOL ((out + initial) + BitVec.ofNat 64 offset)) := by
    intro offset inside
    have address : initial + BitVec.ofNat 64 offset = BitVec.ofNat 64 (initial.toNat + offset) := by
      simp [BitVec.ofNat_add]
    rw [BitVec.add_assoc,address]
    exact outputDomain _ (by omega)
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ :=
    evaluate_compactNibble_nonempty_body state pointer length out initial leaf c0 odd first nonzero byte rfl loaded
      rfl rfl rfl rfl pointerLocal lengthLocal (by simpa using outputDomain 0 (by omega))
      (by omega) (by omega) code suffixSource suffixOutput heapGlobal request finishBound ticks
  refine ⟨result,post,run,cost,remaining,noTimeout,?_⟩
  intro value equal
  obtain ⟨valueEq,valid⟩ := returned value equal
  refine ⟨initial + 2 * (length - 1),leaf,valueEq,?_,leafSmall,valid⟩
  have doubled : (2 * (length - 1)).toNat = 2 * (length - 1).toNat := by
    rw [BitVec.toNat_mul]
    change (2 * (length - 1).toNat) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add_of_lt (by rw [doubled]; omega),doubled]
  omega

#print axioms evaluate_compactNibble_buffer_body
end InitECandidate.Runtime
