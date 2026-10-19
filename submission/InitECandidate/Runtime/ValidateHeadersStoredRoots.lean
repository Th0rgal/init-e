import InitECandidate.Runtime.HeaderPointerPrefix
import InitECandidate.Runtime.ValidateHeadersParentReaches
/-!
The parent records the validation loop has already stored.

`h` is scoped by the actual `decCall`: the frozen call semantics restores the caller's
locals on return, so the decoded record only survives across iterations through the store
`hs[i] = h` that the loop tail performs.  This module therefore carries the parent record in
`hs`, not in `h`.

`ValidateHeadersStoredRoots s hs filled frontier floor` says that every stored pointer cell
`hs + slot * 8`, `slot < filled`, holds a record pointer whose generated state root word is
readable at `pointer + 32`, whose root word address is inside the arena, whose record extent
`pointer .. pointer + 248` lies entirely below `frontier` (the live heap frontier of the same
state), and that starts at or above `floor`.

The two bounds are used for two different jobs and must not be conflated:

* `frontier` is the *live upper* frontier: it is what places a stored record below the heap the
  current iteration allocates from, and it is what the final parent declaration needs;
* `floor` is a *fixed* lower bound, the end of the hash buffer `hashes + count * 32 + 32`.  It is
  the same number in every iteration, so it separates a stored record from the hash output slot
  the tail writes, and - because it lies above the pointer buffer - from the tail's own store
  target as well.

Neither bound is derived from the other: the moving frontier says nothing about where the hash
buffer is, and the floor says nothing about how much room the record still needs.

The lemmas here are the invariant algebra: the component starts empty, is extended by one
actual store of the decoded record, is transported across any run that keeps the stored cells,
their root cells and the memory domain, and is transported across a run whose memory is
unchanged on one window that contains every stored cell and every stored root word.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The stored header pointers below `filled` each carry a readable generated state root word
at `pointer + 32`, that address is inside the arena, the record's 248-byte extent lies below
`frontier`, the live heap frontier of the same state, and the record starts at or above the
fixed `floor`. -/
def ValidateHeadersStoredRoots {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (filled frontier floor : Nat) : Prop :=
  ∀ slot : BitVec 64, slot.toNat < filled →
    ∃ header root : BitVec 64,
      s.memory (hs + slot * (8#64)) = .word header ∧
      s.memory (header + 32#64) = .word root ∧
      s.memaddrs (header + 32#64) ∧
      header.toNat + 248 ≤ frontier ∧
      floor ≤ header.toNat

/-- An empty pointer buffer stores no records. -/
theorem validateHeadersStoredRoots_empty {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (frontier floor : Nat) : ValidateHeadersStoredRoots s hs 0 frontier floor := by
  intro slot inside
  omega

#print axioms validateHeadersStoredRoots_empty

/-- A larger live frontier keeps the component: the stored records still fit below it.  This is
how the component follows the growing heap the loop allocates from. -/
theorem ValidateHeadersStoredRoots.mono {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (filled frontier frontier' floor : Nat) (le : frontier ≤ frontier')
    (roots : ValidateHeadersStoredRoots s hs filled frontier floor) :
    ValidateHeadersStoredRoots s hs filled frontier' floor := by
  intro slot inside
  obtain ⟨header,root,cell,rootCell,rootHere,extent,above⟩ := roots slot inside
  exact ⟨header,root,cell,rootCell,rootHere,by omega,above⟩

#print axioms ValidateHeadersStoredRoots.mono

/-- Store one decoded record at the loop's current slot: the buffer cell is the record
pointer, the record's own root word and domain are the decoder's, the extent sits below the
live frontier and the record starts above the fixed floor, while every earlier cell and
earlier root word is kept. -/
theorem validateHeadersStoredRoots_store {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs index header root : BitVec 64) (frontier floor : Nat)
    (roots : ValidateHeadersStoredRoots s hs index.toNat frontier floor)
    (fits : index.toNat * 8 < 2^64)
    (domain : post.memaddrs = s.memaddrs)
    (cell : post.memory (hs + index * (8#64)) = .word header)
    (rootWord : post.memory (header + 32#64) = .word root)
    (rootDomain : post.memaddrs (header + 32#64))
    (extent : header.toNat + 248 ≤ frontier)
    (aboveFloor : floor ≤ header.toNat)
    (cells : ∀ slot : BitVec 64, slot.toNat < index.toNat →
      post.memory (hs + slot * (8#64)) = s.memory (hs + slot * (8#64)))
    (rootCells : ∀ slot : BitVec 64, slot.toNat < index.toNat → ∀ prior : BitVec 64,
      s.memory (hs + slot * (8#64)) = .word prior → ∀ word : BitVec 64,
        s.memory (prior + 32#64) = .word word → post.memory (prior + 32#64) = .word word) :
    ValidateHeadersStoredRoots post hs (index.toNat + 1) frontier floor := by
  intro slot inside
  by_cases same : slot = index
  · subst same
    exact ⟨header,root,cell,rootWord,rootDomain,extent,aboveFloor⟩
  · have older : slot.toNat < index.toNat := by
      have different : slot.toNat ≠ index.toNat := fun eq => same (BitVec.eq_of_toNat_eq eq)
      omega
    obtain ⟨prior,word,priorCell,priorRoot,priorDomain,priorExtent,priorAbove⟩ := roots slot older
    exact ⟨prior,word,(cells slot older).trans priorCell,
      rootCells slot older prior priorCell word priorRoot,by rw [domain]; exact priorDomain,priorExtent,
      priorAbove⟩

#print axioms validateHeadersStoredRoots_store

/-- Transport the component across any run that keeps the stored cells, their root words and
the memory domain.  The root-word premise is where a tail frame has to say that the heap
records are untouched; everything else is the ordinary domain/memory frame. -/
theorem ValidateHeadersStoredRoots.after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (filled frontier floor : Nat)
    (roots : ValidateHeadersStoredRoots s hs filled frontier floor)
    (domain : post.memaddrs = s.memaddrs)
    (cells : ∀ slot : BitVec 64, slot.toNat < filled →
      post.memory (hs + slot * (8#64)) = s.memory (hs + slot * (8#64)))
    (rootCells : ∀ slot : BitVec 64, slot.toNat < filled → ∀ prior : BitVec 64,
      s.memory (hs + slot * (8#64)) = .word prior → ∀ word : BitVec 64,
        s.memory (prior + 32#64) = .word word → post.memory (prior + 32#64) = .word word) :
    ValidateHeadersStoredRoots post hs filled frontier floor := by
  intro slot inside
  obtain ⟨prior,word,priorCell,priorRoot,priorDomain,priorExtent,priorAbove⟩ := roots slot inside
  exact ⟨prior,word,(cells slot inside).trans priorCell,
    rootCells slot inside prior priorCell word priorRoot,by rw [domain]; exact priorDomain,priorExtent,priorAbove⟩

#print axioms ValidateHeadersStoredRoots.after_frame

/-- Transport the component across a run whose memory is unchanged on the single window
`[ceiling, heap)`.  Both a stored pointer cell and the root word of a stored record have to lie
in that window for the run to preserve them; `floorBelow` says the fixed floor is inside the
arena, which places every stored record above `ceiling`.  This is the shape of the actual
header-decode call: its body rewrites only the memory it allocates, and the loop's pointer
buffer and the records already stored both lie in the window it reports. -/
theorem ValidateHeadersStoredRoots.after_window {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (filled frontier floor ceiling heap : Nat)
    (roots : ValidateHeadersStoredRoots s hs filled frontier floor)
    (domain : post.memaddrs = s.memaddrs)
    (window : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap →
      post.memory address = s.memory address)
    (cellInside : ∀ slot : BitVec 64, slot.toNat < filled →
      ceiling ≤ (hs + slot * (8#64)).toNat ∧ (hs + slot * (8#64)).toNat < heap)
    (rootInside : ∀ prior : BitVec 64, floor ≤ prior.toNat → prior.toNat + 248 ≤ frontier →
      ceiling ≤ (prior + 32#64).toNat ∧ (prior + 32#64).toNat < heap)
    (floorBelow : ceiling ≤ floor) :
    ValidateHeadersStoredRoots post hs filled frontier floor := by
  intro slot inside
  obtain ⟨prior,word,priorCell,priorRoot,priorDomain,priorExtent,priorAbove⟩ := roots slot inside
  obtain ⟨rootLow,rootHigh⟩ := rootInside prior priorAbove priorExtent
  refine ⟨prior,word,(window _ (cellInside slot inside).1 (cellInside slot inside).2).trans priorCell,
    (window _ rootLow rootHigh).trans priorRoot,by rw [domain]; exact priorDomain,priorExtent,priorAbove⟩

#print axioms ValidateHeadersStoredRoots.after_window

/-- The cell the loop reads at the end - `hs[i - 1]` for the actual nonzero index - holds the
last stored parent record with its readable root word, its root domain, its extent below the
live frontier and its position above the fixed floor. -/
theorem ValidateHeadersStoredRoots.last {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs count : BitVec 64) (frontier floor : Nat)
    (roots : ValidateHeadersStoredRoots s hs count.toNat frontier floor) (nonzero : count ≠ 0) :
    ∃ header word : BitVec 64,
      s.memory (hs + (count - 1) * 8) = .word header ∧
      s.memory (header + 32#64) = .word word ∧
      s.memaddrs (header + 32#64) ∧ header.toNat + 248 ≤ frontier ∧ floor ≤ header.toNat := by
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
