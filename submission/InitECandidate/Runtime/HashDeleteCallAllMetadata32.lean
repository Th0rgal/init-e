import InitECandidate.Runtime.HashDeleteCallAll32
import InitECandidate.Runtime.HashDeleteCallMetadata32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion call with reusable table invariants and heap metadata frames. -/
theorem evaluate_hashDelete32_call_all_metadata {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument : ExpHOL 64)
    (table keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (budget : capacity.toNat * 37 + 3 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      state.clock ≤ post.clock + capacity.toNat * 37 + 3 ∧ post.clock ≤ state.clock ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableArraysInvariant32 table keys stride capacity used values order orderPos remaining bits post ∧
        HashValueEntriesWord used values capacity post ∧ HashOrderEntriesBound order capacity remaining post ∧
        HashReverseEntriesBound used orderPos capacity remaining post ∧ HashOrderLinked used order orderPos capacity remaining post) ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,cost,remaining,invariants,locals⟩ := evaluate_hashDelete32_call_all state tableArgument keyArgument table keys stride capacity used values order orderPos items key bits invariant entries reverse ordered linked keyValueOrder keyAligned keyDomain arguments budget
  obtain ⟨checked,checkedRun,_,_,globals,code,domain,endian,_⟩ := evaluate_hashDelete32_call_metadata state tableArgument keyArgument table keys stride capacity used values order orderPos items key bits invariant entries reverse ordered linked keyValueOrder keyAligned keyDomain arguments budget
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  refine ⟨post,run,cost,remaining,invariants,locals,?_,?_,?_,?_⟩
  · rw [same]; exact globals
  · rw [same]; exact code
  · rw [same]; exact domain
  · rw [same]; exact endian

#print axioms evaluate_hashDelete32_call_all_metadata
end InitECandidate.Runtime
