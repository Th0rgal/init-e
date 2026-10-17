import InitECandidate.Runtime.RollbackNewTableRegistryDeclaration
import InitECandidate.Runtime.HashNewHeaderBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Assignment-form constructor calls used after the first local declaration
retain the enlarged registry when updating an existing word local. -/
theorem rollback_htabNew_registry_local_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (keyArgument capacityArgument : ExpHOL 64) (table capacity : BitVec 64) (bits : Nat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word (widths table)),.val (.word capacity)])
    (power : capacity.toNat = 2 ^ bits)
    (tableDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table (widths table) capacity).toNat + capacity.toNat * 8 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : (widths table).toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table (widths table) capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table (widths table) capacity + BitVec.ofNat 64 offset)))
    (large : 1 < capacity.toNat)
    (family : ∀ other ∈ tables, RollbackTableReady widths other state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (name : MlS) (oldValue : BitVec 64)
    (localWord : state.locals.lookup name = some (.val (.word oldValue))) :
    ∃ post, evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,post) ∧
      (∀ other ∈ insert table tables, RollbackTableReady widths other post) ∧
      RollbackPhysicalSeparated widths (insert table tables) post ∧
      post.locals.lookup name = some (.val (.word table)) ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HeapGlobalsFrame state post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)))) ∧
      state.clock ≤ post.clock + capacity.toNat + 8 ∧ post.clock ≤ state.clock := by
  obtain ⟨post,run,registry,apart,cost,remaining,locals,postCode,domain,endian,globalsFrame,postHeap,_,atLocal⟩ := rollback_htabNew_registry_declaration state widths tables
    keyArgument capacityArgument table capacity bits arguments power tableDomain code ticks heap keyBound tableAligned budget
    headerDomain wordDomain byteDomain large family separated
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (widths table)))).update (ofString "cap",.val (.word capacity))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "cap" ≠ ofString "key_len" := by decide
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word (widths table))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyPost,body,_⟩ := evaluate_source_htabNew_header entry table (widths table) capacity code
    (by change capacity.toNat + 7 ≤ state.clock - 1; omega) heap keyBound tableAligned budget keyLocal capLocal
    headerDomain wordDomain byteDomain
  have installed : state.code.lookup (ofString "htab_new") =
      some ([(ofString "key_len",.one),(ofString "cap",.one)],sourceFunctionBody Guest.guestFn_htab_new,.one) := by
    rw [code]; exact originalRuntimeCode_htabNew_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap")
    (sourceFunctionBody Guest.guestFn_htab_new) (widths table) capacity (by decide) installed
  have discarded := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_new")
    [keyArgument,capacityArgument] [.val (.word (widths table)),.val (.word capacity)]
    (sourceFunctionBody Guest.guestFn_htab_new) callee .one (.val (.word table)) bodyPost arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  have same : post = {bodyPost with locals := state.locals} := congrArg Prod.snd (run.symm.trans discarded)
  have valid : isValidValueHOLExact state.toExact .local name (.val (.word table)) = true := by
    simp [isValidValueHOLExact,lookupKvarHOLExact,localWord,shapeOfHOLExact,shapeEqHOL]
  have assigned := evaluateHOLFiniteState_call_return_set_kvar state .local name none (ofString "htab_new")
    [keyArgument,capacityArgument] [.val (.word (widths table)),.val (.word capacity)]
    (sourceFunctionBody Guest.guestFn_htab_new) callee .one (.val (.word table)) bodyPost arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL]) valid
  rw [← same] at assigned
  refine ⟨setVarHOLFinite name (.val (.word table)) post,assigned,(atLocal name).1,(atLocal name).2,?_,postCode,domain,endian,globalsFrame,postHeap,cost,remaining⟩
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms rollback_htabNew_registry_local_call
end InitECandidate.Runtime
