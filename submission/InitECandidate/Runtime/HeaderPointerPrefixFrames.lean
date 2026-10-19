import InitECandidate.Runtime.HeaderPointerPrefix
import InitECandidate.Runtime.ValidateHeadersDecodeReach
/-!
Generic frame transport for the initialized header-pointer buffer.

Root's `HeaderPointerPrefix` records that the first `count` slots of the actual
header-pointer buffer at `hs` are readable word cells.  This module provides
only *conditional* transports: each theorem takes an explicit memory-domain
equality plus an explicit retained-memory hypothesis, and none of them asserts
anything about a particular executed call.

* `HeaderPointerPrefix.after_memory_between` and its `_nat` variant keep the
  buffer for any run that preserves the memory domain and every word of a
  window `[lower, upper)` containing `[hs, hs + count * 8)`.  No per-slot
  hypothesis is needed: every slot address is evaluated exactly, which only
  asks the window to stay below `2^64`.
* `header_pointer_prefix_of_decoder_window` is the shape that matches the
  *exports* of `validate_headers_decode_reaches` (Nat ceiling, unchanged memory
  domain, memory retained on `[ceiling, heap)`).  It is a transport keyed to
  those exported facts, not a proof about the decoder execution itself: a
  caller that has the reach in hand instantiates it with the reach's own domain
  and window components.
* `HeaderPointerPrefix.after_memory_eq` is the degenerate whole-memory case
  (for example scope restoration, or a phase that writes no memory at all).  It
  is *not* the hash phase: the real Keccak/hash steps write separated windows,
  and those are covered by the between-window transports above (or by root's
  dedicated hash wrapper), not by whole-memory preservation.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Conditional transport: the initialized header-pointer buffer survives any
run that keeps the memory domain and every word of the window `[lower, upper)`
(both word bounds), provided that window contains `[hs, hs + count * 8)`. -/
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

/-- Conditional transport with natural-number window bounds, matching the Nat
ceilings and Nat window bounds used by the header-validation reach exports. -/
theorem HeaderPointerPrefix.after_memory_between_nat {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (lower upper count : Nat)
    (initialized : HeaderPointerPrefix s hs count)
    (domain : post.memaddrs = s.memaddrs)
    (below : lower ≤ hs.toNat)
    (above : hs.toNat + count * 8 ≤ upper)
    (upperBound : upper < 2 ^ 64)
    (memory : ∀ address : BitVec 64, lower ≤ address.toNat → address.toNat < upper →
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

/-- Conditional transport in the exact shape of the facts exported by
`validate_headers_decode_reaches`: a Nat `ceiling`, an unchanged memory domain
and memory retained on `[ceiling, heap)`.  Given those facts for any run, the
initialized pointer buffer survives whenever it starts at or above the ceiling
and ends at or below the heap frontier. -/
theorem header_pointer_prefix_of_decoder_window {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs heap : BitVec 64) (ceiling count : Nat)
    (initialized : HeaderPointerPrefix s hs count)
    (below : ceiling ≤ hs.toNat)
    (above : hs.toNat + count * 8 ≤ heap.toNat)
    (domain : post.memaddrs = s.memaddrs)
    (window : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
      post.memory address = s.memory address) :
    HeaderPointerPrefix post hs count :=
  HeaderPointerPrefix.after_memory_between_nat s post hs ceiling heap.toNat count initialized
    domain below above (by omega) window

/-- Conditional transport for a run that keeps the entire memory (for example
scope restoration or a phase with no memory writes).  The real hash/Keccak
steps write separated windows and are handled by the between-window transports
above, not by this whole-memory case. -/
theorem HeaderPointerPrefix.after_memory_eq {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (count : Nat) (initialized : HeaderPointerPrefix s hs count)
    (domain : post.memaddrs = s.memaddrs) (memory : post.memory = s.memory) :
    HeaderPointerPrefix post hs count :=
  HeaderPointerPrefix.after_frame s post hs count initialized domain (fun slot _ => by rw [memory])

#print axioms HeaderPointerPrefix.after_memory_between
#print axioms HeaderPointerPrefix.after_memory_between_nat
#print axioms header_pointer_prefix_of_decoder_window
#print axioms HeaderPointerPrefix.after_memory_eq
end InitECandidate.Runtime
