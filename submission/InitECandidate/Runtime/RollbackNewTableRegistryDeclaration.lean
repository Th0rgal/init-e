import InitECandidate.Runtime.RollbackNewTableRegistry
import InitECandidate.Runtime.RollbackWorldRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual constructor declaration binds its returned pointer for the
continuation with the enlarged separated registry and advanced frontier. -/
theorem rollback_htabNew_registry_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (separated : RollbackPhysicalSeparated widths tables state) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,post) ∧
      (∀ other ∈ insert table tables, RollbackTableReady widths other post) ∧
      RollbackPhysicalSeparated widths (insert table tables) post ∧
      state.clock ≤ post.clock + capacity.toNat + 8 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)))) ∧
      (∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) post) continuation;
           (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) ∧
      (∀ name, (∀ other ∈ insert table tables, RollbackTableReady widths other (setVarHOLFinite name (.val (.word table)) post)) ∧
        RollbackPhysicalSeparated widths (insert table tables) (setVarHOLFinite name (.val (.word table)) post)) := by
  obtain ⟨post,run,registry,apart,cost,remaining⟩ := rollback_htabNew_registry state widths tables
    keyArgument capacityArgument table capacity bits arguments power tableDomain code ticks heap keyBound tableAligned budget
    headerDomain wordDomain byteDomain large family separated
  obtain ⟨checked,checkedRun,_,_,_,_,locals,postCode,domain,endian,newReady,decl⟩ := evaluate_htabNew_ready_frame state
    keyArgument capacityArgument table (widths table) capacity bits arguments power tableDomain code ticks heap keyBound tableAligned budget
    headerDomain wordDomain byteDomain
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at locals postCode domain endian newReady decl
  refine ⟨post,run,registry,apart,cost,remaining,locals,postCode,domain,endian,newReady.live.frontier.heap,decl,?_⟩
  intro name
  exact ⟨fun other member => (registry other member).after_read rfl rfl rfl rfl rfl,
    apart.after_read (after := setVarHOLFinite name (.val (.word table)) post) rfl rfl rfl rfl rfl⟩

#print axioms rollback_htabNew_registry_declaration
end InitECandidate.Runtime
