import InitECandidate.Runtime.HashNewHeaderCall
import InitECandidate.Runtime.HashInsertConstructed32
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual constructor declaration followed by the first insertion,
using the constructor result as its table argument, has a finite linear bound. -/
theorem evaluate_htabNew_first_insert32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (table capacity key value : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (tableAligned : table.toNat % 8 = 0) (keyAligned : key.toNat % 8 = 0)
    (heapBudget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table 32 capacity).toNat + capacity.toNat * 8 → state.memaddrs address)
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table 32 capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table 32 capacity + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 43 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state
        (.decCall name .one (ofString "htab_new") [.const 32,.const capacity]
          (.call (some (none,none)) (ofString "htab_insert_raw") [.var .local name,.const key,.const value])) = (none,post) ∧
      post.memory (table + 24) = .word (1 : BitVec 64) ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table 32 capacity)) = 1 ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 43 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals := by
  obtain ⟨ready,_,empty,newCost,newRemaining,newLocals,newCode,addresses,endian,
      keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField,decl⟩ :=
    evaluate_htabNew_header_call_and_declaration state (.const 32) (.const capacity) table 32 capacity
      (by rfl) code (by omega) heap (by decide) tableAligned heapBudget headerDomain wordDomain byteDomain
  let entered := setVarHOLFinite name (.val (.word table)) ready
  have binding : entered.locals.lookup name = some (.val (.word table)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have arguments : evalListHOLFinite entered
      (h := fun address => Classical.propDecidable (entered.memaddrs address))
      [.var .local name,.const key,.const value] = some [.val (.word table),.val (.word key),.val (.word value)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,binding]
  have domainAfter : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table 32 capacity).toNat + capacity.toNat * 8 → entered.memaddrs address := by
    change ∀ address : BitVec 64, _ → _ → ready.memaddrs address
    rw [addresses]; exact domain
  have wordsAfter : ∀ offset : Nat, offset < 32 → entered.memaddrs (key + BitVec.ofNat 64 offset) := by
    change ∀ offset : Nat, _ → ready.memaddrs _
    rw [addresses]; exact sourceWordDomain
  have bytesAfter : ∀ offset : Nat, offset < 32 → entered.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
    change ∀ offset : Nat, _ → ready.memaddrs _
    rw [addresses]; exact sourceByteDomain
  have agreement : (0 : BitVec 64).toNat = hashOccupiedCount capacity (hashOccupancyRead entered (htabNewUsed table 32 capacity)) := by
    change 0 = hashOccupiedCount capacity (hashOccupancyRead ready (htabNewUsed table 32 capacity))
    exact empty.symm
  have positive : (0 : BitVec 64).toNat < capacity.toNat := by
    change 0 < capacity.toNat
    rw [power]; exact Nat.two_pow_pos bits
  obtain ⟨post,insert,header,count,cost,remaining,locals⟩ := evaluate_hashInsert32_constructed entered
    (.var .local name) (.const key) (.const value) table capacity key value 0 bits (newCode.trans code) power heapBudget domainAfter
    keyField strideField capField countField keysField valuesField usedField orderField reverseField
    agreement positive keyAligned wordsAfter bytesAfter (by change capacity.toNat + 35 ≤ ready.clock; omega) arguments
  rw [decl,insert]
  refine ⟨_,rfl,header,?_,?_,?_,?_⟩
  · change hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table 32 capacity)) = 1
    exact count.symm
  · change state.clock ≤ post.clock + 2 * capacity.toNat + 43
    change ready.clock ≤ post.clock + capacity.toNat + 35 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ ready.clock at remaining
    omega
  · change HolFiniteMapExact.resVarEq post.locals (name,state.locals.lookup name) = state.locals
    have sameLocals : post.locals = (setVarHOLFinite name (.val (.word table)) state).locals := by
      change post.locals = state.locals.update (name,.val (.word table))
      rw [locals]
      change ready.locals.update _ = _
      rw [newLocals]
    exact restore_body_locals state post name (.val (.word table)) sameLocals

#print axioms evaluate_htabNew_first_insert32
end InitECandidate.Runtime
