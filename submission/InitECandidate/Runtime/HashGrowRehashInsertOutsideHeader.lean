import InitECandidate.Runtime.HashGrowRehashInsert
import InitECandidate.Runtime.HashTableOutsideHeaderRegion32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original rehash fragment preserves the earlier allocated region. -/
theorem evaluate_hashGrow_rehash_insert_outside_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count oldKeys oldValues slot : BitVec 64) (bits frontier : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (beforeKeys : frontier ≤ keys.toNat) (beforeValues : frontier ≤ values.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word oldKeys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word oldValues)))
    (slotLocal : state.locals.lookup (ofString "i") = some (.val (.word slot)))
    (countLocal : state.locals.lookup (ofString "k") = some (.val (.word count)))
    (valueDomain : state.memaddrs (oldValues + slot * 8))
    (keyAligned : (oldKeys + slot * stride).toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (oldKeys + slot * stride + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (oldKeys + slot * stride + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + 35 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashGrowRehashInsertAdvance = (none,post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos (count + 1) bits post ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧
      post.locals = (setVarHOLFinite (ofString "k") (.val (.word (count + 1))) state).locals ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64, (watched.toNat < table.toNat ∨ table.toNat + 72 ≤ watched.toNat) → watched.toNat < frontier →
        post.memory watched = state.memory watched := by
  obtain ⟨value,valueMemory⟩ : ∃ value : BitVec 64, state.memory (oldValues + slot * 8) = .word value := by
    cases state.memory (oldValues + slot * 8) with | word value => exact ⟨value,rfl⟩
  have arguments := eval_hashGrow_rehash_arguments state table oldKeys stride oldValues slot value
    tableLocal keysLocal strideLocal valuesLocal slotLocal valueDomain valueMemory
  obtain ⟨inserted,insert,valid,cost,remaining,locals,globals,addresses,endian,frame⟩ :=
    invariant.insert_preserves_outside_header state table keys stride capacity used values order orderPos count (oldKeys + slot * stride) value bits frontier beforeKeys beforeValues
      (.var .local (ofString "t"))
      (.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]])
      (.load .one (hashOrderAddress (ofString "vals") (ofString "i"))) arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
  have binding : inserted.locals.lookup (ofString "k") = some (.val (.word count)) := by rw [locals]; exact countLocal
  have advance := evaluate_hashGrow_rehash_advance inserted count binding
  let post := setVarHOLFinite (ofString "k") (.val (.word (count + 1))) inserted
  refine ⟨post,evaluate_seq_none insert advance,
    valid.after_read inserted post table keys stride capacity used values order orderPos (count + 1) bits rfl rfl rfl rfl,
    cost,remaining,?_,globals,?_,addresses,endian,frame⟩
  · simp only [post,setVarHOLFinite,locals]
  · exact valid.code.trans invariant.code.symm

#print axioms evaluate_hashGrow_rehash_insert_outside_header
end InitECandidate.Runtime
