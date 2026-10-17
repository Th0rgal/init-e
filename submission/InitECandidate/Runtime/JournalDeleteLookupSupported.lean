import InitECandidate.Runtime.JournalDeleteSource32
import InitECandidate.Runtime.HashTableReadyGetCallSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute the original jset lookup prefix and expose its exact continuation. -/
theorem HashTableReady.jdel_lookup_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "t"),.var .local (ofString "key")] =
        some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 3 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
      post.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ other, other ≠ ofString "old" → post.locals.lookup other = state.locals.lookup other) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel) =
        (let output := evaluateHOLFiniteState post journalDeleteAfterGet32;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals ((ofString "old"),state.locals.lookup (ofString "old")))})) := by
  obtain ⟨present,value,post,boolean,postReady,savedLocal,cost,remaining,memory,globals,code,domain,endian,locals,decl⟩ :=
    ready.get_supported_declaration state keyLength table pointer keys stride capacity used values order orderPos items key bits supported
      (ofString "old") (.var .local (ofString "t")) (.var .local (ofString "key")) arguments keyAligned keyWords keyBytes budget
  refine ⟨present,value,post,boolean,postReady,savedLocal,cost,remaining,memory,globals,code,domain,endian,locals,?_⟩
  rw [source_journalDelete32]
  exact decl journalDeleteAfterGet32

#print axioms HashTableReady.jdel_lookup_supported
end InitECandidate.Runtime
