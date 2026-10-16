import InitECandidate.Runtime.HashHasTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original has-table body for aligned32-byte keys, including the
original lookup call and Boolean decision, with unchanged memory. -/
theorem evaluate_source_hashHas32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride key capacity used : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word (32 : BitVec 64))
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ value : BitVec 64, ∃ post, (value = 0 ∨ value = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_has) =
        (some (.returned (.val (.word value))),post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,_,cost,remaining,memory,globals,postCode,addresses,endian,locals,decl⟩ :=
    evaluate_hashFind32_declaration state _ _ table keys stride key capacity used bits code power
      keysAligned strideAligned keyAligned strideFits bounded domain16 cell16 domain0 cell0 domain8 cell8
      domain32 cell32 domain48 cell48 arrayDomain keyDomain readable room arguments budget
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have different : ofString "i" ≠ ofString "t" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using tableLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,boolean,tail⟩ := evaluate_hashHasTail entered table found capacity t i
    (by change ready.memaddrs _; rw [addresses]; exact domain16)
    (by change ready.memory _ = _; rw [memory]; exact cell16)
  rw [source_hashHas_body,decl]
  change ∃ value post, _ ∧ (let output := evaluateHOLFiniteState entered hashHasTail; _) = _ ∧ _
  rw [tail]
  exact ⟨value,_,boolean,rfl,cost,remaining,memory,globals,postCode,addresses,endian⟩

#print axioms evaluate_source_hashHas32
end InitECandidate.Runtime
