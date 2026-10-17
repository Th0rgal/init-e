import InitECandidate.Runtime.HashHasTail
import InitECandidate.Runtime.HashTableArraysFindWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_source_hashHas20 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
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
  obtain ⟨found,ready,_,cost,remaining,memory,globals,postCode,addresses,endian,locals,postArrays,decl⟩ :=
    arrays.find20 state table keys stride capacity used values order orderPos count key bits
      _ _ arguments keyAligned keyWords keyBytes budget
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have different : ofString "i" ≠ ofString "t" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using tableLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,boolean,tail⟩ := evaluate_hashHasTail entered table found capacity t i
    (by change ready.memaddrs _; rw [addresses]; exact arrays.header_domain state 20 table keys stride capacity used values order orderPos count bits 16 (by decide))
    (by change ready.memory _ = _; rw [memory]; exact arrays.cell16)
  rw [source_hashHas_body,decl]
  change ∃ value post, _ ∧ (let output := evaluateHOLFiniteState entered hashHasTail; _) = _ ∧ _
  rw [tail]
  exact ⟨value,_,boolean,rfl,cost,remaining,memory,globals,postCode,addresses,endian⟩


theorem evaluate_source_hashHas52 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
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
  obtain ⟨found,ready,_,cost,remaining,memory,globals,postCode,addresses,endian,locals,postArrays,decl⟩ :=
    arrays.find52 state table keys stride capacity used values order orderPos count key bits
      _ _ arguments keyAligned keyWords keyBytes budget
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have different : ofString "i" ≠ ofString "t" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using tableLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,boolean,tail⟩ := evaluate_hashHasTail entered table found capacity t i
    (by change ready.memaddrs _; rw [addresses]; exact arrays.header_domain state 52 table keys stride capacity used values order orderPos count bits 16 (by decide))
    (by change ready.memory _ = _; rw [memory]; exact arrays.cell16)
  rw [source_hashHas_body,decl]
  change ∃ value post, _ ∧ (let output := evaluateHOLFiniteState entered hashHasTail; _) = _ ∧ _
  rw [tail]
  exact ⟨value,_,boolean,rfl,cost,remaining,memory,globals,postCode,addresses,endian⟩


#print axioms evaluate_source_hashHas20
#print axioms evaluate_source_hashHas52
end InitECandidate.Runtime
