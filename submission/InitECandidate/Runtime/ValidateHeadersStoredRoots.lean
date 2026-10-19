import InitECandidate.Runtime.HeaderPointerPrefix
import InitECandidate.Runtime.ValidateHeadersParentReaches
/-!
The parent records the validation loop has already stored.

`h` is scoped by the actual `decCall`: the frozen call semantics restores the caller's
locals on return, so the decoded record only survives across iterations through the store
`hs[i] = h` that the loop tail performs.  This module therefore carries the parent record in
`hs`, not in `h`.

`ValidateHeadersStoredRoots s hs filled frontier` says that every stored pointer cell
`hs + slot * 8`, `slot < filled`, holds a record pointer whose generated state root word is
readable at `pointer + 32`, whose root word address is inside the arena, and whose record
extent `pointer .. pointer + 248` lies entirely below the frontier of the live heap.  That is
exactly the information the validation loop re-reads from the buffer and the information the
final parent declaration needs.

The lemmas here are the invariant algebra: the component starts empty, is extended by one
actual store of the decoded record, and is transported across any run that keeps the stored
cells, their root cells, and the memory domain.  The one step that is *not* transported for
free by the lead's tail frame is the root word cell of an *older* record: the lead's
`validate_headers_first_tail_normal_frame` preserves `[ceiling, hs)`, while a record lives in
the heap above the frontier.  `ValidateHeadersStoredRoots.after_frame` therefore asks for that
window explicitly, so a tail-level frame (per-store or above-frontier) discharges it without
touching this module.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The stored header pointers below `filled` each carry a readable generated state root word
at `pointer + 32`, that address is inside the arena, and the record's 248-byte extent lies
below `frontier`, the live heap frontier of the same state. -/
def ValidateHeadersStoredRoots {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (filled frontier : Nat) : Prop :=
  ∀ slot : BitVec 64, slot.toNat < filled →
    ∃ header word : BitVec 64,
      s.memory (hs + slot * (8#64)) = .word header ∧
      s.memory (header + 32#64) = .word word ∧
      s.memaddrs (header + 32#64) ∧
      header.toNat + 248 ≤ frontier

/-- An empty pointer buffer stores no records. -/
theorem validateHeadersStoredRoots_empty {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (frontier : Nat) : ValidateHeadersStoredRoots s hs 0 frontier := by
  intro slot inside
  omega

#print axioms validateHeadersStoredRoots_empty

/-- Store one decoded record at the loop's current slot: the buffer cell is the record
pointer, the record's own root word and domain are the decoder's, the extent sits below the
live frontier, and every earlier cell and earlier root word is kept. -/
theorem validateHeadersStoredRoots_store {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs index header word : BitVec 64) (frontier : Nat)
    (roots : ValidateHeadersStoredRoots s hs index.toNat frontier)
    (fits : index.toNat * 8 < 2^64)
    (domain : post.memaddrs = s.memaddrs)
    (cell : post.memory (hs + index * (8#64)) = .word header)
    (rootWord : post.memory (header + 32#64) = .word word)
    (rootDomain : post.memaddrs (header + 32#64))
    (extent : header.toNat + 248 ≤ frontier)
    (cells : ∀ slot : BitVec 64, slot.toNat < index.toNat →
      post.memory (hs + slot * (8#64)) = s.memory (hs + slot * (8#64)))
    (rootCells : ∀ slot : BitVec 64, slot.toNat < index.toNat → ∀ prior : BitVec 64,
      s.memory (hs + slot * (8#64)) = .word prior → ∀ root : BitVec 64,
        s.memory (prior + 32#64) = .word root → post.memory (prior + 32#64) = .word root) :
    ValidateHeadersStoredRoots post hs (index.toNat + 1) frontier := by
  intro slot inside
  by_cases same : slot = index
  · subst same
    exact ⟨header,word,cell,rootWord,rootDomain,extent⟩
  · have older : slot.toNat < index.toNat := by
      have different : slot.toNat ≠ index.toNat := fun eq => same (BitVec.eq_of_toNat_eq eq)
      omega
    obtain ⟨prior,root,priorCell,priorRoot,priorDomain,priorExtent⟩ := roots slot older
    exact ⟨prior,root,(cells slot older).trans priorCell,rootCells slot older prior priorCell root priorRoot,
      by rw [domain]; exact priorDomain,priorExtent⟩

#print axioms validateHeadersStoredRoots_store

/-- Transport the component across any run that keeps the stored cells, their root words and
the memory domain.  The root-word premise is where a tail frame has to say that the heap
records are untouched; everything else is the ordinary domain/memory frame. -/
theorem ValidateHeadersStoredRoots.after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (filled frontier : Nat)
    (roots : ValidateHeadersStoredRoots s hs filled frontier)
    (domain : post.memaddrs = s.memaddrs)
    (cells : ∀ slot : BitVec 64, slot.toNat < filled →
      post.memory (hs + slot * (8#64)) = s.memory (hs + slot * (8#64)))
    (rootCells : ∀ slot : BitVec 64, slot.toNat < filled → ∀ prior : BitVec 64,
      s.memory (hs + slot * (8#64)) = .word prior → ∀ root : BitVec 64,
        s.memory (prior + 32#64) = .word root → post.memory (prior + 32#64) = .word root) :
    ValidateHeadersStoredRoots post hs filled frontier := by
  intro slot inside
  obtain ⟨prior,root,priorCell,priorRoot,priorDomain,priorExtent⟩ := roots slot inside
  exact ⟨prior,root,(cells slot inside).trans priorCell,
    rootCells slot inside prior priorCell root priorRoot,by rw [domain]; exact priorDomain,priorExtent⟩

#print axioms ValidateHeadersStoredRoots.after_frame

/-- The cell the loop reads at the end - `hs[i - 1]` for the actual nonzero index - holds the
last stored parent record with its readable root word, its root domain and its extent below
the live frontier. -/
theorem ValidateHeadersStoredRoots.last {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs count : BitVec 64) (frontier : Nat)
    (roots : ValidateHeadersStoredRoots s hs count.toNat frontier) (nonzero : count ≠ 0) :
    ∃ header word : BitVec 64,
      s.memory (hs + (count - 1) * 8) = .word header ∧
      s.memory (header + 32#64) = .word word ∧
      s.memaddrs (header + 32#64) ∧ header.toNat + 248 ≤ frontier := by
  have positive : 0 < count.toNat := by
    have nz : count.toNat ≠ 0 := by
      intro eq
      exact nonzero (BitVec.eq_of_toNat_eq eq)
    omega
  have indexNat : (count - (1#64)).toNat = count.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by change (1#64 : BitVec 64).toNat ≤ count.toNat; exact positive)]
    rfl
  exact roots (count - (1#64)) (by rw [indexNat]; omega)

#print axioms ValidateHeadersStoredRoots.last
end InitECandidate.Runtime
