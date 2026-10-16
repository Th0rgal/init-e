import InitECandidate.Runtime.HashTableArraysFind32
import InitECandidate.Runtime.HashGetBody32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original value lookup from, and preserving, the reusable table invariant. -/
theorem HashTableArraysInvariant32.get {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_get) =
        (some (.returned (.rStruct [.val (.word present),.val (.word value)])),post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits post := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  have domain16 := HashTableArraysInvariant32.header_domain state table keys stride capacity used values order orderPos count bits invariant 16 (by decide)
  have domain40 := HashTableArraysInvariant32.header_domain state table keys stride capacity used values order orderPos count bits invariant 40 (by decide)
  have cell16 := invariant.cell16
  have cell40 := invariant.cell40
  have facts := invariant.insertion_memory state table keys stride capacity used values order orderPos count bits
  have valueDomain := facts.valueDomain
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,postCode,addresses,endian,locals,_,decl⟩ :=
    HashTableArraysInvariant32.find state table keys stride capacity used values order orderPos count key bits invariant _ _ arguments keyAligned keyDomain budget
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have different : ofString "i" ≠ ofString "t" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using tableLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨present,value,boolean,tail⟩ := evaluate_hashGetTail entered table found capacity values t i inside
    (by change ready.memaddrs _; rw [addresses]; exact domain16)
    (by change ready.memory _ = _; rw [memory]; exact cell16)
    (by change ready.memaddrs _; rw [addresses]; exact domain40)
    (by change ready.memory _ = _; rw [memory]; exact cell40)
    (by intro slot bound; change ready.memaddrs _; rw [addresses]; exact valueDomain slot bound)
  rw [source_hashGet_body,decl]
  change ∃ present value post, _ ∧ (let output := evaluateHOLFiniteState entered hashGetTail; _) = _ ∧ _
  rw [tail]
  exact ⟨present,value,_,boolean,rfl,cost,remaining,memory,globals,postCode,addresses,endian,HashTableArraysInvariant32.after_read state _ table keys stride capacity used values order orderPos count bits invariant memory postCode addresses endian⟩

#print axioms HashTableArraysInvariant32.get
end InitECandidate.Runtime
