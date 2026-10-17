import InitECandidate.Runtime.RollbackNewTableRegistryLocalCall
import InitECandidate.Runtime.HashNewLocalCallBeforeHeader
import InitECandidate.Runtime.StateFreshTxTableStore
import InitECandidate.Runtime.HashNewHeapDomains
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One actual fresh-transaction constructor assignment and following pointer
store, with the complete registry/layout/frontier contract for the next step. -/
theorem evaluate_stateFreshTx_constructor_store_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (oldValue : BitVec 64)
    (localWord : state.locals.lookup (ofString "t") = some (.val (.word oldValue)))
    (ts : BitVec 64) (offset : Nat)
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word ts)))
    (offsetBound : offset < 72)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (headerBefore : ts.toNat + 72 ≤ table.toNat)
    (oldHeaders : ∀ other ∈ tables, ts.toNat + 72 ≤ other.toNat) :
    ∃ post, evaluateHOLFiniteState state
      (.seq (.call (some (some (.local,ofString "t"),none)) (ofString "htab_new") [keyArgument,capacityArgument])
        (.store (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)]) (.var .local (ofString "t")))) = (none,post) ∧
      (∀ other ∈ insert table tables, RollbackTableReady widths other post) ∧ RollbackPhysicalSeparated widths (insert table tables) post ∧
      (∀ other ∈ insert table tables, ts.toNat + 72 ≤ other.toNat) ∧
      post.locals.lookup (ofString "t") = some (.val (.word table)) ∧
      post.memory (ts + BitVec.ofNat 64 offset) = .word table ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HeapGlobalsFrame state post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)))) ∧
      state.clock ≤ post.clock + capacity.toNat + 8 ∧ post.clock ≤ state.clock ∧
      ∀ address : BitVec 64, address.toNat < table.toNat → address ≠ ts + BitVec.ofNat 64 offset →
        post.memory address = state.memory address := by
  obtain ⟨tableDomain,headerDomain,wordDomain,byteDomain⟩ := htabNew_heap_domains state table (widths table) capacity keyBound budget heapDomain
  have tsBound : ts.toNat + 72 ≤ 33806089496 := by omega
  have slotDomain : state.memaddrs (ts + BitVec.ofNat 64 offset) := by
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have address : (ts + BitVec.ofNat 64 offset).toNat = ts.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    exact heapDomain _ (by omega)
  obtain ⟨created,creation,registry,apart,tLocal,postCode,addresses,endian,globals,heapNext,cost,remaining⟩ :=
    rollback_htabNew_registry_local_call state widths tables keyArgument capacityArgument table capacity bits arguments power tableDomain code ticks heap
      keyBound tableAligned budget headerDomain wordDomain byteDomain large family separated (ofString "t") oldValue localWord
  obtain ⟨framed,framedRun,_,_,memoryFrame⟩ :=
    evaluate_htabNew_local_call_before_header state keyArgument capacityArgument table (widths table) capacity
      arguments code ticks heap keyBound tableAligned budget headerDomain wordDomain byteDomain
      (ofString "t") oldValue localWord
  have same : created = framed := congrArg Prod.snd (creation.symm.trans framedRun)
  have createdFrame : ∀ address : BitVec 64, address.toNat < table.toNat →
      created.memory address = state.memory address := by
    rw [same]; exact memoryFrame
  have headers : ∀ other ∈ insert table tables, ts.toNat + 72 ≤ other.toNat := by
    intro other member
    rcases Set.mem_insert_iff.mp member with same | old
    · simpa only [same] using headerBefore
    · exact oldHeaders other old
  have tsAfter : created.globals.lookup (ofString "ts") = some (.val (.word ts)) :=
    (globals (ofString "ts") (by decide)).trans tsGlobal
  obtain ⟨post,store,postRegistry,postApart,stored,clock,locals,postGlobals,codeEq,domainEq⟩ :=
    evaluate_stateFreshTx_table_store created widths (insert table tables) ts table offset tsAfter tLocal offsetBound tsBound
      (by rw [addresses]; exact slotDomain) registry apart headers
  have exactStore : post = sourceWriteWord created (ts + BitVec.ofNat 64 offset) table := by
    have canonical := evaluate_store_word created (ts + BitVec.ofNat 64 offset) table
      (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)]) (.var .local (ofString "t"))
      (by simp [evalHOLExact,evalListHOLExact,tsAfter,wordOpHOL,wordOp,valueIsWord,valueWord]) tLocal
      (by rw [addresses]; exact slotDomain)
    exact congrArg Prod.snd (store.symm.trans canonical)
  have postEndian : post.be = state.be := by rw [exactStore]; exact endian
  have framed : HeapGlobalsFrame state post := globals.trans (HeapGlobalsFrame.of_globals postGlobals)
  refine ⟨post,evaluate_seq_none creation store,postRegistry,postApart,headers,by rw [locals]; exact tLocal,
    stored,codeEq.trans postCode,domainEq.trans addresses,postEndian,framed,by rw [postGlobals]; exact heapNext,by omega,by omega,?_⟩
  intro address before outside
  rw [exactStore]
  simp only [sourceWriteWord,if_neg outside]
  exact createdFrame address before

#print axioms evaluate_stateFreshTx_constructor_store_memory_frame
end InitECandidate.Runtime
