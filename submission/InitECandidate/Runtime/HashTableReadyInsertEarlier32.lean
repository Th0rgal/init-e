import InitECandidate.Runtime.HashTableInsertEarlierTable32
import InitECandidate.Runtime.HashTableReadyIntervalFrame32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual insertion preserves an earlier allocated table even when it lies
between the target header and the target's relocated arrays. -/
theorem HashTableReady32.insert_with_earlier_table {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos count bits pointer state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + 35 ≤ state.clock)
    (otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state)
    (beforeKeys : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ keys.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat)
    (separateHeader : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨
      table.toNat + 72 ≤ otherTable.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableReady32 table keys stride capacity used values order orderPos (count + 1) bits pointer post ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer post ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,valid,ordered,words,reverse,linked,cost,remaining,locals,globals,domain,endian⟩ :=
    ready.live.arrays.insert_all_entries_linked state table keys stride capacity used values order orderPos count key value bits
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
      ready.live.entries ready.valuesWord ready.reverse ready.linked ready.ordering
  obtain ⟨checked,checkedRun,_,otherValid,_⟩ :=
    ready.live.arrays.insert_preserves_earlier_table state table keys stride capacity used values order orderPos count key value bits
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
      otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
      otherReady beforeKeys beforeValues separateHeader
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at otherValid
  exact ⟨post,run,⟨⟨valid,ordered,ready.live.frontier.after_globals state post orderPos capacity pointer globals⟩,
    words,reverse,linked,ready.ordering⟩,otherValid,cost,remaining,locals,globals,domain,endian⟩

#print axioms HashTableReady32.insert_with_earlier_table
end InitECandidate.Runtime
