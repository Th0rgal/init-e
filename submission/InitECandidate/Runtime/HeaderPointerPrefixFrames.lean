import InitECandidate.Runtime.HeaderPointerPrefix
import InitECandidate.Runtime.ValidateHeadersDecodeReach
/-!
Frame transfer for the initialized header-pointer buffer.

Root's `HeaderPointerPrefix` records that the first `count` slots of the actual
header-pointer buffer at `hs` are readable word cells.  Here the prefix is
transported across the real decoder/hash frames:

* `HeaderPointerPrefix.after_memory_between` keeps it whenever the memory
  domain is unchanged and every cell of `[hs, hs + count * 8)` keeps its word,
  expressed as a retained window `[lower, upper)` with `lower <= hs` and
  `hs + count * 8 <= upper`, so no per-slot hypothesis is needed;
* `header_pointer_prefix_of_decoder_window` is the instantiation that matches
  the exports of `validate_headers_decode_reaches` verbatim (unchanged domain
  and memory retained on `[ceiling, heap)`), so the prefix survives a real
  returned header decoder whenever the buffer ends at or below the entry heap
  frontier and starts at or above the scratch ceiling;
* `HeaderPointerPrefix.after_memory_eq` covers calls that keep the whole
  memory (the hash/Keccak phases), and `HeaderPointerPrefix.after_frame` is
  root's per-slot form.

No callee frame or runtime bound is assumed beyond the explicit domain,
window and geometry premises.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The initialized header-pointer buffer survives any run that keeps the
memory domain and every word of the window `[lower, upper)` containing the
whole buffer `[hs, hs + count * 8)`. -/
theorem HeaderPointerPrefix.after_memory_between {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs lower upper : BitVec 64) (count : Nat)
    (initialized : HeaderPointerPrefix s hs count)
    (domain : post.memaddrs = s.memaddrs)
    (below : lower.toNat ≤ hs.toNat)
    (above : hs.toNat + count * 8 ≤ upper.toNat)
    (memory : ∀ address : BitVec 64, lower.toNat ≤ address.toNat → address.toNat < upper.toNat →
      post.memory address = s.memory address) :
    HeaderPointerPrefix post hs count := by
  intro slot inside
  obtain ⟨readable,header,word⟩ := initialized slot inside
  have eight : (8#64 : BitVec 64).toNat = 8 := by decide
  have product : slot.toNat * 8 < 2 ^ 64 := by omega
  have cellValue : (hs + slot * (8#64)).toNat = hs.toNat + slot.toNat * 8 := by
    rw [BitVec.toNat_add,BitVec.toNat_mul,eight]
    rw [Nat.mod_eq_of_lt product]
    rw [Nat.mod_eq_of_lt (by omega : hs.toNat + slot.toNat * 8 < 2 ^ 64)]
  exact ⟨by rw [domain]; exact readable,header,
    (memory _ (by rw [cellValue]; omega) (by rw [cellValue]; omega)).trans word⟩

/-- A run that keeps the whole memory keeps the initialized pointer buffer. -/
theorem HeaderPointerPrefix.after_memory_eq {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (count : Nat) (initialized : HeaderPointerPrefix s hs count)
    (domain : post.memaddrs = s.memaddrs) (memory : post.memory = s.memory) :
    HeaderPointerPrefix post hs count :=
  HeaderPointerPrefix.after_frame s post hs count initialized domain (fun slot _ => by rw [memory])

/-- The initialized header-pointer buffer survives the real returned header
decoder: `validate_headers_decode_reaches` exports an unchanged memory domain
and memory retained on `[ceiling, heap)`, so a buffer starting at or above the
ceiling and ending at or below the entry heap frontier is untouched. -/
theorem header_pointer_prefix_of_decoder_window {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs ceiling heap : BitVec 64) (count : Nat)
    (initialized : HeaderPointerPrefix s hs count)
    (below : ceiling.toNat ≤ hs.toNat)
    (above : hs.toNat + count * 8 ≤ heap.toNat)
    (domain : post.memaddrs = s.memaddrs)
    (window : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
      post.memory address = s.memory address) :
    HeaderPointerPrefix post hs count :=
  HeaderPointerPrefix.after_memory_between s post hs ceiling heap count initialized domain below above
    (fun address low high => window address (BitVec.le_def.mpr (by simpa using low)) high)

#print axioms HeaderPointerPrefix.after_memory_between
#print axioms HeaderPointerPrefix.after_memory_eq
#print axioms header_pointer_prefix_of_decoder_window
end InitECandidate.Runtime
