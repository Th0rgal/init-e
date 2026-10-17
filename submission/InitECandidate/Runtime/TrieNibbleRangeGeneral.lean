import InitECandidate.Runtime.TrieNibbleStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Appending a small byte extends any valid prefix whose new length fits.
Distinct bytes
remain intact even when the append shares their aligned memory word. -/
theorem TrieNibbleRange.append_byte_no_wrap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (nibs length value cell : BitVec 64)
    (valid : TrieNibbleRange state nibs length)
    (bounded : length.toNat + 1 < 2^64) (small : value.toNat < 16)
    (domain : state.memaddrs (panByteAlignHOL (nibs + length)))
    (memory : state.memory (panByteAlignHOL (nibs + length)) = .word cell) :
    TrieNibbleRange (sourceWriteByte state (nibs + length) value cell) nibs (length + 1) := by
  have next : (length + 1).toNat = length.toNat + 1 := by
    rw [BitVec.toNat_add]
    change (length.toNat + 1) % 18446744073709551616 = length.toNat + 1
    omega
  intro offset inside byte loaded
  rw [next] at inside
  by_cases last : offset = length.toNat
  · subst offset
    have read := sourceWriteByte_load_self state (nibs + length) value cell domain
    have same : BitVec.ofNat 64 length.toNat = length := by simp
    change @panMemLoadByteHOL 64 _ (sourceWriteByte state (nibs + length) value cell).memory
      state.memaddrs (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (nibs + BitVec.ofNat 64 length.toNat) = some byte at loaded
    rw [same,read] at loaded
    have equal := Option.some.inj loaded
    subst byte
    change (BitVec.ofNat 8 value.toNat).toNat < 16
    simp only [BitVec.toNat_ofNat]
    omega
  · have earlier : offset < length.toNat := by omega
    have different : nibs + BitVec.ofNat 64 offset ≠ nibs + length := by
      intro equal
      have equalWords : BitVec.ofNat 64 offset = length := by simpa using equal
      have equalNats := congrArg BitVec.toNat equalWords
      simp only [BitVec.toNat_ofNat] at equalNats
      omega
    have unchanged := sourceWriteByte_load_other state (nibs + length) value cell
      (nibs + BitVec.ofNat 64 offset) different memory
    apply valid offset earlier byte
    change @panMemLoadByteHOL 64 _ (sourceWriteByte state (nibs + length) value cell).memory
      state.memaddrs (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (nibs + BitVec.ofNat 64 offset) = some byte at loaded
    exact unchanged.symm.trans loaded

/-- A successful source store at the prefix endpoint both executes the
original evaluator and extends the nibble invariant. -/
theorem evaluate_nibble_append_no_wrap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination expression : Flapjack.Pancake.PanLang.ExpHOL 64)
    (nibs length value cell : BitVec 64)
    (valid : TrieNibbleRange state nibs length)
    (bounded : length.toNat + 1 < 2^64) (small : value.toNat < 16)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) destination =
        some (.val (.word (nibs + length))))
    (valueEval : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
        some (.val (.word value)))
    (domain : state.memaddrs (panByteAlignHOL (nibs + length)))
    (memory : state.memory (panByteAlignHOL (nibs + length)) = .word cell) :
    ∃ post, evaluateHOLFiniteState state (.storeByte destination expression) = (none,post) ∧
      TrieNibbleRange post nibs (length + 1) ∧ post.clock = state.clock := by
  exact ⟨_,evaluate_source_storeByte state destination expression (nibs + length) value cell
    addressEval valueEval domain memory,
    TrieNibbleRange.append_byte_no_wrap state nibs length value cell valid bounded small domain memory,rfl⟩

/-- A shorter prefix inherits nibble validity without reading extra memory. -/
theorem TrieNibbleRange.prefix {F : Type} {state : PanSemStateFiniteExact 64 F}
    {nibs length shorter : BitVec 64} (valid : TrieNibbleRange state nibs length)
    (bounded : shorter.toNat ≤ length.toNat) : TrieNibbleRange state nibs shorter := by
  intro offset inside byte loaded
  exact valid offset (by omega) byte loaded

/-- Pointer slicing preserves readable nibble values. Only the logical index
sum must fit; pointer arithmetic follows the original modular semantics. -/
theorem TrieNibbleRange.slice {F : Type} {state : PanSemStateFiniteExact 64 F}
    {nibs length start count : BitVec 64} (valid : TrieNibbleRange state nibs length)
    (bounded : start.toNat + count.toNat ≤ length.toNat) :
    TrieNibbleRange state (nibs + start) count := by
  intro offset inside byte loaded
  apply valid (start.toNat + offset) (by omega) byte
  simpa [BitVec.ofNat_add,BitVec.add_assoc] using loaded

/-- The suffix expressions used by splitting retain the same nibble range. -/
theorem TrieNibbleRange.suffix {F : Type} {state : PanSemStateFiniteExact 64 F}
    {nibs length start : BitVec 64} (valid : TrieNibbleRange state nibs length)
    (bounded : start.toNat ≤ length.toNat) :
    TrieNibbleRange state (nibs + start) (length - start) := by
  apply valid.slice
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr bounded)]
  omega

#print axioms TrieNibbleRange.prefix
#print axioms TrieNibbleRange.slice
#print axioms TrieNibbleRange.suffix
#print axioms evaluate_nibble_append_no_wrap
#print axioms TrieNibbleRange.append_byte_no_wrap
end InitECandidate.Runtime
