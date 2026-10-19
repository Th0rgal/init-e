import InitECandidate.Runtime.DecodeWitnessRootComparison
import InitECandidate.Runtime.HtabFindSlotBound
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual empty-root comparison is bounded for every pointer alignment and
memory domain. Failed reads terminate; a checked return reaches the guard with
its actual word and unchanged caller memory and globals. -/
theorem decode_witness_root_comparison_bounded_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (root emptyRoot : BitVec 64)
    (atRoot : s.locals.lookup (ofString "root_hash") = some (.val (.word root)))
    (atEmpty : s.globals.lookup (ofString "empty_trie_root") = some (.val (.word emptyRoot)))
    (code : s.code = originalRuntimeCode) (budget : 129 ≤ s.clock) :
    Reaches s (decodeWitnessAt 0)
      (fun post => ∃ word : BitVec 64,
        post.locals = s.locals.update (ofString "is_empty",.val (.word word)) ∧
        post.memory = s.memory ∧ post.globals = s.globals ∧ post.code = s.code ∧
        post.memaddrs = s.memaddrs ∧ post.be = s.be) 129 (decodeWitnessAt 1) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "a",.val (.word root))).update
      (ofString "b",.val (.word emptyRoot))).update (ofString "n",.val (.word (32#64)))
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "root_hash"),.var .global (ofString "empty_trie_root"),.const 32] =
      some [.val (.word root),.val (.word emptyRoot),.val (.word (32#64))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atRoot,atEmpty]
  have lookup : lookupCodeHOLFinite s.code.lookup (ofString "memeq")
      [.val (.word root),.val (.word emptyRoot),.val (.word (32#64))] =
      some (sourceFunctionBody Guest.guestFn_memeq,callee,.one) := by
    rw [code]
    exact pan_three_word_lookup _ _ _ _ _ _ root emptyRoot 32 (by decide) (by decide) (by decide)
      originalRuntimeCode_memeq_lookup
  have nLocal : entry.locals.lookup (ofString "n") = some (.val (.word (32#64))) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,spent,remaining,safe⟩ := evaluate_memeq_body64_bounded_cap entry 32 nLocal
    (by decide) (by change 128 ≤ s.clock - 1; omega)
  have bounded : RunBounded entry (sourceFunctionBody Guest.guestFn_memeq) 128 := by
    unfold RunBounded
    rw [run]
    exact ⟨spent,remaining,safe⟩
  rw [source_decode_witness_root_comparison]
  apply bounded_decCall_reaches s (ofString "is_empty") (ofString "memeq") .one .one _ _
    (sourceFunctionBody Guest.guestFn_memeq) (decodeWitnessAt 1) callee 128 _ args lookup budget bounded
  intro value bodyPost bodyRun checked
  obtain ⟨word,rfl⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checked.1)
  have memory := evaluate_readOnly_memory _ memeq_readOnlyMemory entry
  have globals := evaluate_readOnly_globals _ memeq_readOnlyMemory entry
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_memeq)
  rw [bodyRun] at memory globals metadata
  exact ⟨word,rfl,memory,globals,metadata.1,metadata.2.1,metadata.2.2.1⟩

#print axioms decode_witness_root_comparison_bounded_reaches
end InitECandidate.Runtime
