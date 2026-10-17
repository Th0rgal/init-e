import InitECandidate.Runtime.TransactionStorageTableExactSpaceRegisteredValuesIn
import InitECandidate.Runtime.TransactionStorageLinkValueRegisteredValuesIn
import InitECandidate.Runtime.StateStorageInnerSelection
import InitECandidate.Runtime.LocalCallSuccessOtherLocals
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual missing-inner branch creates and registers its32-byte-key table,
links it, then writes the value. Constructor space is explicit; later allocation
failures are included in the bound and cannot imitate successful returns. -/
theorem TransactionRegistryWorld.storage_new_inner_exact_space_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer outer addr key a b c d oldInner lookupValue : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (outerMember : outer ∈ tables)
    (innerLocal : state.locals.lookup (ofString "inner") = some (.val (.word oldInner)))
    (outerLocal : state.locals.lookup (ofString "outer") = some (.val (.word outer)))
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word addr)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word lookupValue)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (space : pointer.toNat + 528 ≤ 33806089496)
    (addrAligned : addr.toNat % 8 = 0) (keyAligned : key.toNat % 8 = 0)
    (addrWords : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (addr + BitVec.ofNat 64 offset))
    (addrBytes : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (panByteAlignHOL (addr + BitVec.ofNat 64 offset)))
    (keyWords : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (ticks : 2 ^ 76 + 19 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageInnerSelection = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 76 + 19) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TransactionRegistryWorld (withTableWidth widths pointer 32)
        (insert pointer tables) fieldPointer ts journal snapshot ((count + 1) + 1) post ∧
        (∀ other ∈ watched, HashTableValuesIn other (insert pointer targets) post) ∧
        JournalSavedValuesIn journal ((count + 1) + 1).toNat watched (insert pointer targets) post) := by
  let constructor : ProgHOL 64 := .call (some (some (.local,ofString "inner"),none)) (ofString "htab_new") [.const 32,.const 8]
  let link : ProgHOL 64 := .call (some (none,none)) (ofString "jset")
    [.var .local (ofString "outer"),.var .local (ofString "addr"),.var .local (ofString "inner")]
  obtain ⟨middle,creation,midValid,midValues,midSaved,cost,remaining,atInner,_⟩ := valid.new_storage_table_local_exact_space_registered_values_in state widths tables
    fieldPointer ts journal snapshot count pointer oldInner (ofString "inner") innerLocal heap watched targets watchedSubset registered saved space (by omega)
  have locals := evaluate_local_call_success_other_locals state (ofString "htab_new") (ofString "inner") [.const 32,.const 8]
    (by rw [show evaluateHOLFiniteState state _ = (none,middle) from creation])
  change ∀ name, name ≠ ofString "inner" → (evaluateHOLFiniteState state constructor).2.locals.lookup name = state.locals.lookup name at locals
  rw [creation] at locals
  have metadata := evaluateHOLFiniteState_metadata state constructor
  rw [creation] at metadata
  have domain : middle.memaddrs = state.memaddrs := metadata.2.1
  have oldHeader := valid.journalWorld.world.registered_header_before_frontier pointer outer outerMember heap
  have different : outer ≠ pointer := by intro same; rw [same] at oldHeader; omega
  have outerWidth : withTableWidth widths pointer 32 outer = widths outer := by simp only [withTableWidth,if_neg different]
  have innerWidth : withTableWidth widths pointer 32 pointer = (32 : BitVec 64) := by simp [withTableWidth]
  have innerNat : (withTableWidth widths pointer 32 pointer).toNat = 32 := by rw [innerWidth]; rfl
  have pointerUnwatched : pointer ∉ watched := by
    intro belongs
    have header := valid.journalWorld.world.registered_header_before_frontier pointer pointer (watchedSubset belongs) heap
    omega
  obtain ⟨result,post,run,tailCost,tailRemaining,noTimeout,preserved⟩ := midValid.storage_link_and_value_registered_values_in middle
    (withTableWidth widths pointer 32) (insert pointer tables) fieldPointer ts journal snapshot count outer pointer addr key a b c d
    (Set.mem_insert_of_mem pointer outerMember) (Set.mem_insert pointer tables)
    ((locals (ofString "outer") (by decide)).trans outerLocal) atInner ((locals (ofString "addr") (by decide)).trans addrLocal)
    ((locals (ofString "key") (by decide)).trans keyLocal) ((locals (ofString "value") (by decide)).trans valueLocal)
    addrAligned keyAligned (by simpa only [domain,outerWidth] using addrWords) (by simpa only [domain,outerWidth] using addrBytes)
    (by simpa only [domain,innerNat] using keyWords) (by simpa only [domain,innerNat] using keyBytes) watched (insert pointer targets)
      (fun other belongs => Set.mem_insert_of_mem pointer (watchedSubset belongs)) midValues midSaved
      (fun _ => Set.mem_insert pointer targets) pointerUnwatched (by omega)
  have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
    simp [evalHOLExact,mLocal,Compiler.Encoders.Asm.wordCmpHOL]
  have selected : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0)) (.seq constructor link)
        (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m"))))) =
      evaluateHOLFiniteState state (.seq constructor link) := by
    rw [evaluateHOLFiniteState_ite,condition]
    rfl
  have sequence : evaluateHOLFiniteState state stateStorageInnerSelection =
      evaluateHOLFiniteState state (.seq constructor stateStorageLinkAndValue) := by
    calc
      _ = evaluateHOLFiniteState state (.seq (.seq constructor link) stateStorageValueTail) := by
        change evaluateHOLFiniteState state (.seq
          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0)) (.seq constructor link)
            (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m"))))) stateStorageValueTail) = _
        rw [evaluateHOLFiniteState_seq_line780]
        conv_rhs => rw [evaluateHOLFiniteState_seq_line780]
        rw [selected]
      _ = _ := evaluate_seq_assoc state constructor link stateStorageValueTail
  exact ⟨result,post,sequence.trans (evaluate_seq_none creation run),by omega,by omega,noTimeout,preserved⟩

#print axioms TransactionRegistryWorld.storage_new_inner_exact_space_registered_values_in
end InitECandidate.Runtime
