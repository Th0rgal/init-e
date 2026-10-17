import InitECandidate.Runtime.HashTableArraysAllEntries32
import InitECandidate.Runtime.HashInsertCallLinked32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Insertion preserves the allocated layout, entry bounds and live order linkage together. -/
theorem HashTableArraysInvariant32.insert_all_entries_linked {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + 35 ≤ state.clock)
    (entries : HashOrderEntriesBound order capacity count state)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (linked : HashOrderLinked used order orderPos capacity count state)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos (count + 1) bits post ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      HashValueEntriesWord used values capacity post ∧
      HashReverseEntriesBound used orderPos capacity (count + 1) post ∧
      HashOrderLinked used order orderPos capacity (count + 1) post ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,valid,ordered,words,reverse,cost,remaining,locals,globals,addresses,endian⟩ :=
    invariant.insert_all_entries state table keys stride capacity used values order orderPos count key value bits
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
      entries valueEntries reverseEntries keysBeforeValues
  obtain ⟨checked,checkedRun,_,_,postLinked,_⟩ := evaluate_hashInsert32_call_linked state
    tableArgument keyArgument valueArgument capacity used table values value order orderPos count keys stride key bits
    budget invariant keyAligned sourceWordDomain sourceByteDomain arguments linked
  have equal : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  refine ⟨post,run,valid,ordered,words,reverse,?_,cost,remaining,locals,globals,addresses,endian⟩
  rw [equal]
  exact postLinked

#print axioms HashTableArraysInvariant32.insert_all_entries_linked
end InitECandidate.Runtime
