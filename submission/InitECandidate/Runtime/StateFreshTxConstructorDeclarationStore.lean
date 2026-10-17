import InitECandidate.Runtime.RollbackNewTableRegistryDeclaration
import InitECandidate.Runtime.StateFreshTxTableStore
import InitECandidate.Runtime.HashNewHeapDomains
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One actual fresh-transaction constructor assignment and following pointer
store, with the complete registry/layout/frontier contract for the next step. -/
theorem evaluate_stateFreshTx_constructor_declaration_store {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (keyArgument capacityArgument : ExpHOL 64) (table capacity : BitVec 64) (bits : Nat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word (widths table)),.val (.word capacity)])
    (power : capacity.toNat = 2 ^ bits)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : (widths table).toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (large : 1 < capacity.toNat)
    (family : ∀ other ∈ tables, RollbackTableReady widths other state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (ts : BitVec 64) (offset : Nat)
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word ts)))
    (offsetBound : offset < 72)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (headerBefore : ts.toNat + 72 ≤ table.toNat)
    (oldHeaders : ∀ other ∈ tables, ts.toNat + 72 ≤ other.toNat) :
    ∃ post, (∀ tail, evaluateHOLFiniteState state
      (.decCall (ofString "t") .one (ofString "htab_new") [keyArgument,capacityArgument]
        (.seq (.store (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)]) (.var .local (ofString "t"))) tail)) =
      (let output := evaluateHOLFiniteState post tail;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "t",state.locals.lookup (ofString "t"))}))) ∧
      (∀ other ∈ insert table tables, RollbackTableReady widths other post) ∧ RollbackPhysicalSeparated widths (insert table tables) post ∧
      (∀ other ∈ insert table tables, ts.toNat + 72 ≤ other.toNat) ∧
      post.locals.lookup (ofString "t") = some (.val (.word table)) ∧
      post.memory (ts + BitVec.ofNat 64 offset) = .word table ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HeapGlobalsFrame state post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)))) ∧
      state.clock ≤ post.clock + capacity.toNat + 8 ∧ post.clock ≤ state.clock := by
  obtain ⟨tableDomain,headerDomain,wordDomain,byteDomain⟩ := htabNew_heap_domains state table (widths table) capacity keyBound budget heapDomain
  have tsBound : ts.toNat + 72 ≤ 33806089496 := by omega
  have slotDomain : state.memaddrs (ts + BitVec.ofNat 64 offset) := by
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have address : (ts + BitVec.ofNat 64 offset).toNat = ts.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    exact heapDomain _ (by omega)
  obtain ⟨created,_,registry,apart,cost,remaining,_,postCode,addresses,endian,globals,heapNext,decl,atLocal⟩ :=
    rollback_htabNew_registry_declaration state widths tables keyArgument capacityArgument table capacity bits arguments power tableDomain code ticks heap
      keyBound tableAligned budget headerDomain wordDomain byteDomain large family separated
  let entered := setVarHOLFinite (ofString "t") (.val (.word table)) created
  have tLocal : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have headers : ∀ other ∈ insert table tables, ts.toNat + 72 ≤ other.toNat := by
    intro other member
    rcases Set.mem_insert_iff.mp member with same | old
    · simpa only [same] using headerBefore
    · exact oldHeaders other old
  have tsAfter : entered.globals.lookup (ofString "ts") = some (.val (.word ts)) :=
    (globals (ofString "ts") (by decide)).trans tsGlobal
  obtain ⟨post,store,postRegistry,postApart,stored,clock,locals,postGlobals,codeEq,domainEq⟩ :=
    evaluate_stateFreshTx_table_store entered widths (insert table tables) ts table offset tsAfter tLocal offsetBound tsBound
      (by change created.memaddrs _; rw [addresses]; exact slotDomain) (atLocal (ofString "t")).1 (atLocal (ofString "t")).2 headers
  have exactStore : post = sourceWriteWord entered (ts + BitVec.ofNat 64 offset) table := by
    have canonical := evaluate_store_word entered (ts + BitVec.ofNat 64 offset) table
      (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)]) (.var .local (ofString "t"))
      (by simp [evalHOLExact,evalListHOLExact,tsAfter,wordOpHOL,wordOp,valueIsWord,valueWord]) tLocal
      (by change created.memaddrs _; rw [addresses]; exact slotDomain)
    exact congrArg Prod.snd (store.symm.trans canonical)
  have enteredClock : entered.clock = created.clock := rfl
  have postEndian : post.be = state.be := by rw [exactStore]; exact endian
  have framed : HeapGlobalsFrame state post := globals.trans (HeapGlobalsFrame.of_globals postGlobals)
  refine ⟨post,?_,postRegistry,postApart,headers,by rw [locals]; exact tLocal,
    stored,codeEq.trans postCode,domainEq.trans addresses,postEndian,framed,by rw [postGlobals]; exact heapNext,by omega,by omega⟩
  intro tail
  rw [decl]
  change (let output := evaluateHOLFiniteState entered (.seq (.store (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)]) (.var .local (ofString "t"))) tail); _) = _
  rw [evaluateHOLFiniteState_seq_line780,store]

#print axioms evaluate_stateFreshTx_constructor_declaration_store
end InitECandidate.Runtime
