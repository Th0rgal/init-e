import InitECandidate.Runtime.JournalSetSource32
import InitECandidate.Runtime.HashTableReadyGetCall32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute the original jset lookup prefix and expose its exact continuation. -/
theorem HashTableReady32.jset_lookup {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "t"),.var .local (ofString "key")] =
        some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : 2 * capacity.toNat + 3 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post ∧
      post.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ other, other ≠ ofString "old" → post.locals.lookup other = state.locals.lookup other) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset) =
        (let output := evaluateHOLFiniteState post journalSetAfterGet32;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals ((ofString "old"),state.locals.lookup (ofString "old")))})) := by
  obtain ⟨present,value,post,boolean,postReady,savedLocal,cost,remaining,memory,globals,code,domain,endian,locals,decl⟩ :=
    ready.get_declaration state table pointer keys stride capacity used values order orderPos items key bits
      (ofString "old") (.var .local (ofString "t")) (.var .local (ofString "key")) arguments keyAligned keyDomain budget
  refine ⟨present,value,post,boolean,postReady,savedLocal,cost,remaining,memory,globals,code,domain,endian,locals,?_⟩
  rw [source_journalSet32]
  exact decl journalSetAfterGet32

#print axioms HashTableReady32.jset_lookup
end InitECandidate.Runtime
