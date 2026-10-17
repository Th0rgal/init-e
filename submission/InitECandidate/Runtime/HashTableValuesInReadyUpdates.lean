import InitECandidate.Runtime.HashTableReadyInsertPhysicalFrameSupported
import InitECandidate.Runtime.HashTableSetExistingPhysicalFrame
import InitECandidate.Runtime.HashTableValuesInInsertCall
import InitECandidate.Runtime.HashTableValuesInExisting
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual insertion/update output combines its full ready invariant,
registered-value membership and physical memory frame. -/
theorem HashTableReady.insert_supported_values_in_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets)
 :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos (count + 1) bits pointer post ∧
      HashTableValuesIn table targets post ∧
      (∀ address : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order orderPos address →
        post.memory address = state.memory address) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,valid,frame,cost,remaining,locals,globals,domain,endian⟩ :=
    ready.insert_supported_with_physical_frame state keyLength table pointer keys stride capacity used values order orderPos count key value bits supported
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
  obtain ⟨checked,checkedRun,_,_,_,_,registered,_,_,_,_,_⟩ :=
    evaluate_hashInsert_call_values_in state tableArgument keyArgument valueArgument capacity used table values value order orderPos count keys stride key keyLength bits
      supported budget ready.live.arrays keyAligned sourceWordDomain sourceByteDomain ready.ordering arguments targets entries member
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  exact ⟨post,run,valid,by rw [same]; exact registered,frame,cost,remaining,locals,globals,domain,endian⟩

/-- The actual insertion/update output combines its full ready invariant,
registered-value membership and physical memory frame. -/
theorem HashTableReady.set_existing_values_in_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items index value : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (i : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (inside : index.toNat < capacity.toNat) (missing : ProgHOL 64)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets)
 :
    ∃ post, evaluateHOLFiniteState state (hashSetExistingTail missing) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
      HashTableValuesIn table targets post ∧
      (∀ address : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order orderPos address →
        post.memory address = state.memory address) ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,valid,frame,clock,globals,code,domain,endian⟩ :=
    ready.set_existing_with_physical_frame state keyLength table pointer keys stride capacity used values order orderPos items index value bits t i v inside missing
  obtain ⟨checked,checkedRun,_,registered,_⟩ :=
    ready.set_existing_values_in state keyLength table pointer keys stride capacity used values order orderPos items index value bits
      targets entries member t i v inside missing
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  exact ⟨post,run,valid,by rw [same]; exact registered,frame,clock,globals,code,domain,endian⟩

#print axioms HashTableReady.insert_supported_values_in_frame
#print axioms HashTableReady.set_existing_values_in_frame
end InitECandidate.Runtime
