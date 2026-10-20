import InitECandidate.Runtime.MptNibbleUnsecuredDeclarationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptSetAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_mpt_set)

theorem source_mpt_set_key_prefix : sourceFunctionBody Guest.guestFn_mpt_set=
 .decCall (ofString "nk") (.comb [.one,.one]) (ofString "mpt_nibble_key")
  [.var .local (ofString "m"),.var .local (ofString "key"),.var .local (ofString "klen")] (mptSetAt 1) := by
 rw [sourceFunctionBody_eq_structural]
 rfl

/-- The actual indexed-key path through mpt_set obtains at most eighteen
nibbles in at most nine source clocks, including real allocation failure and
invalid-access outcomes. Successful allocation guards are earned in the
reached-state contract; no input-buffer or heap-room assumption is used. -/
theorem mpt_set_indexed_key_prefix_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (table key length pointer : BitVec 64)
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0) (short : length.toNat≤9)
 (code : s.code=originalRuntimeCode) (budget : 9≤s.clock) :
 Reaches s (sourceFunctionBody Guest.guestFn_mpt_set)
  (fun next=>MptNibbleUnsecuredDeclarationReady s next (ofString "nk") pointer length ∧
   (2*length).toNat≤18) 9 (mptSetAt 1) := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "m"),.var .local (ofString "key"),.var .local (ofString "klen")]=
  some [.val (.word table),.val (.word key),.val (.word length)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atTable,atKey,atLength]
 have actual:=mpt_nibble_unsecured_declaration_reaches s (ofString "nk") _ (mptSetAt 1)
  table key length pointer args atHeap unsecured (by omega) code (by omega)
 rw [←source_mpt_set_key_prefix] at actual
 apply reaches_mono s _ (mptSetAt 1) _ _ _ 9 (by omega) _ actual
 intro next ready
 refine ⟨ready,?_⟩
 change (2#64*length).toNat≤18
 rw [BitVec.toNat_mul]
 change (2*length.toNat)%2^64≤18
 rw [Nat.mod_eq_of_lt (by omega)]
 omega

#print axioms source_mpt_set_key_prefix
#print axioms mpt_set_indexed_key_prefix_reaches
end InitECandidate.Runtime
