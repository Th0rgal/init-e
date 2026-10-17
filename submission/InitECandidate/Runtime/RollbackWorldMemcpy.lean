import InitECandidate.Runtime.RollbackRegistryMemcpy
import InitECandidate.Runtime.RollbackWorldFrame
import InitECandidate.Runtime.JournalUndoRecordIntervals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Copying a newly allocated key beyond all live arrays and records preserves
 the complete rollback world, with explicit source-clock and caller frames. -/
theorem RollbackWorld.memcpy_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (witness : BitVec 64)
    (member : witness ∈ tables)
    (journal snapshot count : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (destinationArgument sourceArgument sizeArgument : ExpHOL 64) (destination source size : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (aligned : destination.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0) (budget : size.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (outside : ∀ table ∈ tables, ∀ pointer keys stride capacity used values order reverse items bits,
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits pointer state →
      reverse.toNat + capacity.toNat * 8 ≤ destination.toNat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [destinationArgument,sourceArgument,sizeArgument] =
        some [.val (.word destination),.val (.word source),.val (.word size)])
    (journalBefore : journal.toNat + count.toNat * 32 ≤ destination.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy")
        [destinationArgument,sourceArgument,sizeArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals := by
  obtain ⟨post,run,family,apart,cost,remaining,globals,code,domain,endian,locals,memory⟩ :=
    rollback_registry_memcpy state widths tables witness member world.ready separated destinationArgument sourceArgument sizeArgument destination source size
      small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain outside arguments
  have journalBound : journal.toNat + count.toNat * 32 ≤ 33806089496 := by omega
  have frame : ∀ index : Nat, index < count.toNat → ∀ offset ∈ ([0,8,16,24] : List Nat),
      post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
      state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) := by
    intro index inside offset belongs
    have smallOffset : offset < 32 := by simp at belongs; omega
    have interval := journal_undo_field_interval journal count.toNat index offset journalBound inside smallOffset
    exact memory _ (Or.inl (by omega))
  have preserved := world.after_frame (Nat.le_refl _) (after := post)
    (by rw [globals]; exact world.counter) (by rw [locals]; exact world.snapshotLocal)
    (by rw [globals]; exact world.journalGlobal) domain frame family
  exact ⟨post,run,preserved,apart,cost,remaining,globals,code,domain,endian,locals⟩

#print axioms RollbackWorld.memcpy_preserves
end InitECandidate.Runtime
