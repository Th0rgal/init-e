import InitECandidate.Runtime.HashDeleteCallAllMetadataSupported
import InitECandidate.Runtime.HashTableReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.delete_call_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : capacity.toNat * 57 + 3 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos remaining bits pointer post) ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + 3 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,cost,remaining,⟨count,counts,arrays,words,ordered,reverse,linked⟩,locals,globals,code,domain,endian⟩ :=
    evaluate_hashDelete_supported_call_all_metadata state tableArgument keyArgument keyLength table keys stride capacity used values order orderPos items key bits supported
      ready.live.arrays ready.valuesWord ready.reverse ready.live.entries ready.linked ready.ordering keyAligned keyWords keyBytes arguments budget
  exact ⟨post,run,⟨count,counts,⟨⟨arrays,ordered,ready.live.frontier.after_globals state post orderPos capacity pointer globals⟩,
    words,reverse,linked,ready.ordering⟩⟩,cost,remaining,locals,globals,code,domain,endian⟩

#print axioms HashTableReady.delete_call_supported
end InitECandidate.Runtime
