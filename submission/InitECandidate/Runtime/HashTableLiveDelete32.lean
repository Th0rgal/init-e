import InitECandidate.Runtime.HashTableLive32
import InitECandidate.Runtime.HashDeleteCallAllMetadata32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Deletion preserves the live table and its heap frontier without allocating. -/
theorem HashTableLive32.delete_call_all {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (live : HashTableLive32 table keys stride capacity used values order orderPos items bits pointer state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : capacity.toNat * 37 + 3 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableLive32 table keys stride capacity used values order orderPos remaining bits pointer post ∧
        HashValueEntriesWord used values capacity post ∧ HashReverseEntriesBound used orderPos capacity remaining post ∧
        HashOrderLinked used order orderPos capacity remaining post) ∧
      state.clock ≤ post.clock + capacity.toNat * 37 + 3 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,cost,remaining,⟨count,counts,arrays,words,ordered,reverseEntries,postLinked⟩,locals,globals,code,domain,endian⟩ :=
    evaluate_hashDelete32_call_all_metadata state tableArgument keyArgument table keys stride capacity used values order orderPos items key bits
      live.arrays entries reverse live.entries linked keyValueOrder keyAligned keyDomain arguments budget
  exact ⟨post,run,⟨count,counts,⟨arrays,ordered,live.frontier.after_globals state post orderPos capacity pointer globals⟩,
    words,reverseEntries,postLinked⟩,cost,remaining,locals,globals,code,domain,endian⟩

#print axioms HashTableLive32.delete_call_all
end InitECandidate.Runtime
