import InitECandidate.Runtime.RollbackNewTableSafePlan
import InitECandidate.Runtime.RollbackNewTableRegistryDeclaration
import InitECandidate.Runtime.HashNewGlobalsSafePlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual safe-plan constructor declaration retains global state outside
heap_ptr and exposes the enlarged separated registry to its continuation. -/
theorem rollback_htabNew_registry_declaration_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (pointerBound : table.toNat ≤ 33806089496)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes (widths table) capacity))
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table (widths table) capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table (widths table) capacity + BitVec.ofNat 64 offset)))
    (large : 1 < capacity.toNat)
    (family : ∀ other ∈ tables, RollbackTableReady widths other state)
    (separated : RollbackPhysicalSeparated widths tables state) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,post) ∧
      (∀ other ∈ insert table tables, RollbackTableReady widths other post) ∧
      RollbackPhysicalSeparated widths (insert table tables) post ∧
      state.clock ≤ post.clock + capacity.toNat + 8 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HeapGlobalsFrame state post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)))) ∧
      (∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) post) continuation;
           (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) ∧
      (∀ name, (∀ other ∈ insert table tables, RollbackTableReady widths other (setVarHOLFinite name (.val (.word table)) post)) ∧
        RollbackPhysicalSeparated widths (insert table tables) (setVarHOLFinite name (.val (.word table)) post)) := by
  obtain ⟨post,run,registry,apart,cost,remaining⟩ := rollback_htabNew_registry_of_safe_plan state widths tables
    keyArgument capacityArgument table capacity bits arguments power tableDomain code ticks heap keyBound tableAligned pointerBound fullSafe
    headerDomain wordDomain byteDomain large family separated
  obtain ⟨checked,checkedRun,_,_,_,_,locals,postCode,domain,endian,newReady,decl⟩ := evaluate_htabNew_ready_frame_of_safe_plan state
    keyArgument capacityArgument table (widths table) capacity bits arguments power tableDomain code ticks heap keyBound tableAligned pointerBound fullSafe
    headerDomain wordDomain byteDomain
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at locals postCode domain endian newReady decl
  obtain ⟨framed,framedRun,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,globalsFrame,_⟩ :=
    evaluate_htabNew_header_call_and_declaration_heap_frame_of_safe_plan state keyArgument capacityArgument table (widths table) capacity arguments
      code ticks heap pointerBound tableAligned fullSafe headerDomain wordDomain byteDomain
  have sameFramed : post = framed := congrArg Prod.snd (run.symm.trans framedRun)
  rw [← sameFramed] at globalsFrame
  refine ⟨post,run,registry,apart,cost,remaining,locals,postCode,domain,endian,globalsFrame,newReady.live.frontier.heap,decl,?_⟩
  intro name
  exact ⟨fun other member => (registry other member).after_read rfl rfl rfl rfl rfl,
    apart.after_read (after := setVarHOLFinite name (.val (.word table)) post) rfl rfl rfl rfl rfl⟩

#print axioms rollback_htabNew_registry_declaration_of_safe_plan
end InitECandidate.Runtime
