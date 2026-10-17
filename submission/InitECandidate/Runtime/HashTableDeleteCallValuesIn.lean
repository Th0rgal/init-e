import InitECandidate.Runtime.HashDeleteCallValuesIn
import InitECandidate.Runtime.HashTableReadyDeleteSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual htab_del call preserves full table readiness and registered values, with its original runtime and caller frames. -/
theorem HashTableReady.delete_call_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : capacity.toNat * 57 + 3 ≤ state.clock)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos remaining bits pointer post) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + 3 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,target,cost,remaining,locals,globals,code,domain,endian⟩ :=
    ready.delete_call_supported state keyLength table pointer keys stride capacity used values order orderPos items key bits supported
      tableArgument keyArgument arguments keyAligned keyWords keyBytes budget
  obtain ⟨checked,checkedRun,preserved,_⟩ := evaluate_hashDelete_call_values_in state tableArgument keyArgument
    keyLength table keys stride capacity used values order orderPos items key bits supported ready.live.arrays ready.valuesWord ready.reverse ready.live.entries ready.linked ready.ordering
    keyAligned keyWords keyBytes arguments targets registered budget
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  exact ⟨post,run,target,by rw [same]; exact preserved,cost,remaining,locals,globals,code,domain,endian⟩

#print axioms HashTableReady.delete_call_values_in
end InitECandidate.Runtime
