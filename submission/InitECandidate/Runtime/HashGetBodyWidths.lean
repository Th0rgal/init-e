import InitECandidate.Runtime.HashGetTail
import InitECandidate.Runtime.HashTableArraysFindWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_source_hashGet20 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_get) =
        (some (.returned (.rStruct [.val (.word present),.val (.word value)])),post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,postCode,addresses,endian,locals,postArrays,decl⟩ :=
    arrays.find20 state table keys stride capacity used values order orderPos count key bits
      _ _ arguments keyAligned keyWords keyBytes budget
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have different : ofString "i" ≠ ofString "t" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using tableLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨present,value,boolean,tail⟩ := evaluate_hashGetTail entered table found capacity values t i inside
    (by change ready.memaddrs _; rw [addresses]; exact arrays.header_domain state 20 table keys stride capacity used values order orderPos count bits 16 (by decide))
    (by change ready.memory _ = _; rw [memory]; exact arrays.cell16)
    (by change ready.memaddrs _; rw [addresses]; exact arrays.header_domain state 20 table keys stride capacity used values order orderPos count bits 40 (by decide))
    (by change ready.memory _ = _; rw [memory]; exact arrays.cell40)
    (by intro slot bound; change ready.memaddrs _; rw [addresses]; exact (arrays.insertion_memory state 20 table keys stride capacity used values order orderPos count bits).valueDomain slot bound)
  rw [source_hashGet_body,decl]
  change ∃ present value post, _ ∧ (let output := evaluateHOLFiniteState entered hashGetTail; _) = _ ∧ _
  rw [tail]
  exact ⟨present,value,_,boolean,rfl,cost,remaining,memory,globals,postCode,addresses,endian⟩


theorem evaluate_source_hashGet52 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_get) =
        (some (.returned (.rStruct [.val (.word present),.val (.word value)])),post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,postCode,addresses,endian,locals,postArrays,decl⟩ :=
    arrays.find52 state table keys stride capacity used values order orderPos count key bits
      _ _ arguments keyAligned keyWords keyBytes budget
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have different : ofString "i" ≠ ofString "t" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using tableLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨present,value,boolean,tail⟩ := evaluate_hashGetTail entered table found capacity values t i inside
    (by change ready.memaddrs _; rw [addresses]; exact arrays.header_domain state 52 table keys stride capacity used values order orderPos count bits 16 (by decide))
    (by change ready.memory _ = _; rw [memory]; exact arrays.cell16)
    (by change ready.memaddrs _; rw [addresses]; exact arrays.header_domain state 52 table keys stride capacity used values order orderPos count bits 40 (by decide))
    (by change ready.memory _ = _; rw [memory]; exact arrays.cell40)
    (by intro slot bound; change ready.memaddrs _; rw [addresses]; exact (arrays.insertion_memory state 52 table keys stride capacity used values order orderPos count bits).valueDomain slot bound)
  rw [source_hashGet_body,decl]
  change ∃ present value post, _ ∧ (let output := evaluateHOLFiniteState entered hashGetTail; _) = _ ∧ _
  rw [tail]
  exact ⟨present,value,_,boolean,rfl,cost,remaining,memory,globals,postCode,addresses,endian⟩


#print axioms evaluate_source_hashGet20
#print axioms evaluate_source_hashGet52
end InitECandidate.Runtime
