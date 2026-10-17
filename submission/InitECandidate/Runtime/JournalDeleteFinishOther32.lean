import InitECandidate.Runtime.JournalDeleteSource32
import InitECandidate.Runtime.HashTableDeleteCallOther32
import InitECandidate.Runtime.HashTableReadyGlobals32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original journal-delete suffix preserves all reusable table facts and
returns zero within the deletion call's source-clock bound. -/
theorem HashTableReady32.jdel_finish_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key count : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨
      otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat)
    (budget : capacity.toNat * 37 + 3 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state journalDeleteFinish32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos remaining bits pointer post) ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + capacity.toNat * 37 + 3 ∧ post.clock ≤ state.clock ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (count + 1))) ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let incremented := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count + 1))) state
  have nextReady := ready.after_global state table pointer keys stride capacity used values order orderPos items bits
    (ofString "journal_n") (.val (.word (count + 1))) (by decide)
  have arguments : evalListHOLFinite incremented (h := fun address => Classical.propDecidable (incremented.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [incremented,setGlobalHOLFinite,evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k]
  have nextOther := otherReady.after_global state otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
    (ofString "journal_n") (.val (.word (count + 1))) (by decide)
  obtain ⟨post,run,⟨remaining,counts,postReady⟩,preserved,cost,remainingClock,_,globals,code,domain,endian⟩ :=
    nextReady.delete_call_with_other incremented table pointer keys stride capacity used values order orderPos items key bits
      (.var .local (ofString "t")) (.var .local (ofString "key")) arguments keyAligned keyDomain budget
      otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits nextOther separated
  have returned : evaluateHOLFiniteState post (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite post,evaluate_seq_none (evaluate_journal_increment32 state count countGlobal)
    (evaluate_seq_none run returned),⟨remaining,counts,
      postReady.after_read post _ table keys stride capacity used values order orderPos remaining bits pointer rfl rfl rfl rfl rfl⟩,
    preserved.after_read post _ otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl,
    cost,remainingClock,?_,code,domain,endian⟩
  change post.globals.lookup (ofString "journal_n") = _
  rw [globals]
  simp [incremented,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms HashTableReady32.jdel_finish_with_other
end InitECandidate.Runtime
