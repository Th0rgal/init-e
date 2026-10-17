import InitECandidate.Runtime.HashTableArraysLinkedInsertSupported
import InitECandidate.Runtime.HashTableReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual insertion preserves the complete shared mixed-operation invariant. -/
theorem HashTableReady.insert_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat)
    (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
      [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos (count + 1) bits pointer post ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,arrays,entries,words,reverse,linked,cost,remaining,locals,globals,domain,endian⟩ :=
    ready.live.arrays.insert_supported_all_entries_linked state keyLength table keys stride capacity used values order orderPos count key value bits supported
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
      ready.live.entries ready.valuesWord ready.reverse ready.linked ready.ordering
  exact ⟨post,run,⟨⟨arrays,entries,ready.live.frontier.after_globals state post orderPos capacity pointer globals⟩,
    words,reverse,linked,ready.ordering⟩,cost,remaining,locals,globals,domain,endian⟩

#print axioms HashTableReady.insert_supported
end InitECandidate.Runtime
