import InitECandidate.Runtime.HashTableArraysFind32
import InitECandidate.Runtime.HashHasBody32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original membership body retains the reusable table invariant. -/
theorem HashTableArraysInvariant32.has {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ value : BitVec 64, ∃ post, (value = 0 ∨ value = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_has) =
        (some (.returned (.val (.word value))),post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits post := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  have domain16 := HashTableArraysInvariant32.header_domain state table keys stride capacity used values order orderPos count bits invariant 16 (by decide)
  have cell16 := invariant.cell16
  obtain ⟨found,ready,_,cost,remaining,memory,globals,postCode,addresses,endian,locals,_,decl⟩ :=
    HashTableArraysInvariant32.find state table keys stride capacity used values order orderPos count key bits invariant _ _ arguments keyAligned keyDomain budget
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
  exact ⟨value,_,boolean,rfl,cost,remaining,memory,globals,postCode,addresses,endian,HashTableArraysInvariant32.after_read state _ table keys stride capacity used values order orderPos count bits invariant memory postCode addresses endian⟩

#print axioms HashTableArraysInvariant32.has
end InitECandidate.Runtime
