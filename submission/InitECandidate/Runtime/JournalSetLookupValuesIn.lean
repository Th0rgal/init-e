import InitECandidate.Runtime.HashGetCallValueProperty
import InitECandidate.Runtime.HashTableValuesIn
import InitECandidate.Runtime.JournalSetSource32
import InitECandidate.Runtime.HashTableReadyGetCallSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute the original jset lookup prefix and expose its exact continuation. -/
theorem HashTableReady.jset_lookup_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "t"),.var .local (ofString "key")] =
        some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 3 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      (present ≠ 0 → value ∈ targets) ∧ HashTableValuesIn table targets post ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
      post.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ other, other ≠ ofString "old" → post.locals.lookup other = state.locals.lookup other) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset) =
        (let output := evaluateHOLFiniteState post journalSetAfterGet32;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals ((ofString "old"),state.locals.lookup (ofString "old")))})) := by
  obtain ⟨present,value,lookupState,boolean,_,cost,remaining,locals,memory,globals,code,domain,endian,member,decl⟩ :=
    ready.live.arrays.get_value_property state keyLength table keys stride capacity used values order orderPos items key bits
      (fun value => value ∈ targets) supported (.var .local (ofString "t")) (.var .local (ofString "key")) arguments keyAligned keyWords keyBytes
      (registered capacity used values ready.live.arrays.cell16 ready.live.arrays.cell48 ready.live.arrays.cell40) budget
  let post := setVarHOLFinite (ofString "old") (.rStruct [.val (.word present),.val (.word value)]) lookupState
  refine ⟨present,value,post,boolean,member,registered.after_read memory domain endian,
    ready.after_read state post keyLength table keys stride capacity used values order orderPos items bits pointer memory globals code domain endian,
    ?_,cost,remaining,memory,globals,code,domain,endian,?_,?_⟩
  · simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro other different
    simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  · rw [source_journalSet32]
    exact decl (ofString "old") journalSetAfterGet32

#print axioms HashTableReady.jset_lookup_values_in
end InitECandidate.Runtime
