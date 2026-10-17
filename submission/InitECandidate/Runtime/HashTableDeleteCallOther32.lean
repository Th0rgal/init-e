import InitECandidate.Runtime.HashDeleteCallOther32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual deletion call retains both ready tables for subsequent operations. -/
theorem HashTableReady32.delete_call_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : capacity.toNat * 37 + 3 ≤ state.clock)
    (otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨
      otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos remaining bits pointer post) ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + capacity.toNat * 37 + 3 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,target,cost,remaining,locals,globals,code,domain,endian⟩ :=
    ready.delete_call state table pointer keys stride capacity used values order orderPos items key bits
      tableArgument keyArgument arguments keyAligned keyDomain budget
  obtain ⟨checked,checkedRun,preserved,_,_,_,_,_,_,_⟩ := evaluate_hashDelete32_call_with_other state tableArgument keyArgument
    table keys stride capacity used values order orderPos items key bits ready.live.arrays ready.valuesWord ready.reverse ready.live.entries ready.linked ready.ordering
    keyAligned keyDomain arguments
    otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady separated budget
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  exact ⟨post,run,target,by rw [same]; exact preserved,cost,remaining,locals,globals,code,domain,endian⟩

#print axioms HashTableReady32.delete_call_with_other
end InitECandidate.Runtime
