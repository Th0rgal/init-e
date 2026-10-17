import InitECandidate.Runtime.HashInsertIndexLinked32
import InitECandidate.Runtime.HashInsertHashEntries32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual hash call and insertion preserve live order linkage across local scopes. -/
theorem evaluate_hashInsert_hash_linked32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count keys stride key : BitVec 64) (bits : Nat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (budget : capacity.toNat + 34 ≤ state.clock)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (sourceAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (linked : HashOrderLinked used order orderPos capacity count state) :
    ∃ post, evaluateHOLFiniteState state hashInsertHashScope =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      state.clock ≤ post.clock + capacity.toNat + 34 ∧ post.clock ≤ state.clock ∧
      HashOrderLinked used order orderPos capacity (count + 1) post := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word key),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,keyLocal,lengthLocal]
  have hashDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    apply sourceWordDomain
    simp at member
    omega
  obtain ⟨hash,hashed,clock,memory,globals,postCode,addresses,endian,locals,decl⟩ :=
    evaluate_hash32_declaration state _ _ key arguments invariant.code (by omega) sourceAligned hashDomain
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) hashed
  have other : ∀ name, name ≠ ofString "h" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have h : entered.locals.lookup (ofString "h") = some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredInvariant := invariant.after_read state entered table keys stride capacity used values order orderPos count bits
    memory postCode addresses endian
  have ticks : entered.clock = state.clock - 1 := clock
  obtain ⟨post,tail,cost,remaining,postLinked⟩ :=
    evaluate_hashInsert_index_linked32 entered capacity used table values value order orderPos count hash keys stride key bits
      ((other _ (by decide)).trans tableLocal) ((other _ (by decide)).trans orderLocal)
      ((other _ (by decide)).trans orderPosLocal) ((other _ (by decide)).trans valueLocal)
      h ((other _ (by decide)).trans capacityLocal) ((other _ (by decide)).trans usedLocal)
      ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
      ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans lengthLocal)
      (by change capacity.toNat + 32 + 1 ≤ entered.clock; omega) enteredInvariant sourceAligned
      (by change ∀ offset : Nat, _ → hashed.memaddrs _; rw [addresses]; exact sourceWordDomain)
      (by change ∀ offset : Nat, _ → hashed.memaddrs _; rw [addresses]; exact sourceByteDomain)
      (linked.after_read state entered used order orderPos capacity count memory addresses endian)
  unfold hashInsertHashScope
  rw [decl]
  change ∃ post, (let output := evaluateHOLFiniteState entered hashInsertIndexScope; _) = _ ∧ _
  rw [tail]
  refine ⟨_,rfl,?_,?_,?_⟩
  · change state.clock ≤ post.clock + capacity.toNat + 34; omega
  · change post.clock ≤ state.clock; omega
  · exact postLinked.after_read post _ used order orderPos capacity (count + 1) rfl rfl rfl

#print axioms evaluate_hashInsert_hash_linked32
end InitECandidate.Runtime
