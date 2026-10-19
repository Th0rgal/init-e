import InitECandidate.Runtime.NodedbLookupTailSlice
import InitECandidate.Runtime.NodedbTableGetValues
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem missing_tail {F : Type} (s : PanSemStateFiniteExact 64 F) (record : BitVec 64)
    (atResult : s.locals.lookup (ofString "r") = some (.rStruct [.val (.word (0#64)),.val (.word record)])) :
    evaluateHOLFiniteState s nodedbLookupTail =
      (some (.returned (.rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))])),
        emptyLocalsHOLFinite s) := by
  unfold nodedbLookupTail sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_nodedb_lookup,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil]
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,evalListHOLExact,atResult,Compiler.Encoders.Asm.wordCmpHOL,
    evaluateHOLFiniteState_return,shapeOfHOLExact]

/-- The complete original database lookup returns either the missing triple or
a source/length pair inside the original input. Membership and slice data are
carried through its actual hash-get call, rather than assumed at its return. -/
theorem nodedb_lookup_returned_slice {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table heap total key array input inputLength : BitVec 64)
    (built : NodedbTableAt s table heap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (code : s.code = originalRuntimeCode)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atKey : s.locals.lookup (ofString "hash") = some (.val (.word key))) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_nodedb_lookup) =
      (some (.returned v),post)) :
    v = .rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))] ∨
      ∃ pointer length : BitVec 64,
        v = .rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length)] ∧
        input.toNat ≤ pointer.toNat ∧ pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat ∧
        pointer.toNat + length.toNat < 2 ^ 64 ∧ length.toNat ≤ inputLength.toNat := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "db"),.var .local (ofString "hash")] =
      some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atTable,atKey]
  have lookup : lookupCodeHOLFinite s.code.lookup (ofString "htab_get")
      [.val (.word table),.val (.word key)] =
      some (sourceFunctionBody Guest.guestFn_htab_get,callee,.comb [.one,.one]) := by
    rw [code]
    exact pan_two_word_result_lookup originalRuntimeCode.lookup (ofString "htab_get")
      (ofString "t") (ofString "key") (sourceFunctionBody Guest.guestFn_htab_get) table key
      (.comb [.one,.one]) (by decide) originalRuntimeCode_hashGet_lookup
  rw [source_nodedb_lookup_body] at run
  obtain ⟨result,bodyPost,output,bodyRun,_,tail,_⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "r") (ofString "htab_get")
      (.comb [.one,.one]) (.comb [.one,.one]) _ _ (sourceFunctionBody Guest.guestFn_htab_get)
      nodedbLookupTail callee v args lookup run
  have entryBuilt : NodedbTableAt entry table heap total := by
    obtain ⟨k,sd,c,u,val,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := built
    exact ⟨k,sd,c,u,val,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
  obtain ⟨present,record,shape,_,member⟩ := nodedb_table_get_returned_values entry bodyPost table heap total key
    (NodedbSliceTargets array total) entryBuilt (entries.after_read rfl rfl rfl)
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]) result bodyRun
  subst result
  have memory := (htabGet_memoryFrame entry code).1
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_get)
  rw [bodyRun] at memory metadata
  let ready := setVarHOLFinite (ofString "r") (.rStruct [.val (.word present),.val (.word record)])
    {bodyPost with locals := s.locals}
  have atResult : ready.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word present),.val (.word record)]) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  by_cases zero : present = 0
  · subst present
    have actual := missing_tail ready record atResult
    have same := congrArg Prod.fst (tail.symm.trans actual)
    exact Or.inl (by simpa using same)
  · have readySlices : RlpSliceInputPrefix ready array input inputLength total.toNat := by
      intro index inside
      obtain ⟨pointer,length,slice⟩ := slices index inside
      exact ⟨pointer,length,slice.after_frame s ready array index pointer length input inputLength
        metadata.2.1 (congrFun memory _) (congrFun memory _)⟩
    obtain ⟨pointer,length,actual,lo,hi,nowrap,bound⟩ := nodedb_lookup_tail_registry_slice ready present record
      array total input inputLength zero atResult (member zero) readySlices
    have same := congrArg Prod.fst (tail.symm.trans actual)
    exact Or.inr ⟨pointer,length,by simpa using same,lo,hi,nowrap,bound⟩

#print axioms nodedb_lookup_returned_slice
end InitECandidate.Runtime
