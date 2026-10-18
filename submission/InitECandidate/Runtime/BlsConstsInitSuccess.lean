import InitECandidate.Runtime.BlsInitSource
import InitECandidate.Runtime.Bn254AccelInitSuccess
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

/-- Every constant-table offset is below 7136. -/
theorem blsConstsCells_offset : ∀ cell ∈ blsConstsCells, cell.1.toNat < 7136 := by
  have all : blsConstsCells.all (fun cell => decide (cell.1.toNat < 7136)) = true := by decide_cbv
  intro cell member
  simpa using List.all_eq_true.mp all cell member

theorem blsDiscountCells_offset : ∀ cell ∈ blsDiscountCells, cell.1.toNat < 2048 := by
  have all : blsDiscountCells.all (fun cell => decide (cell.1.toNat < 2048)) = true := by decide_cbv
  intro cell member
  simpa using List.all_eq_true.mp all cell member

#print axioms blsConstsCells_offset
/-- First bls_consts_init from heap H: bls_c = H, heap H+7136 (H aligned), the
892 literal words written, two ticks for the call. -/
theorem evaluate_blsConstsInit_call_first {F : Type} (state : PanSemStateFiniteExact 64 F) (H : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (aligned : H.toNat % 8 = 0) (room : H.toNat + 7136 + 7 ≤ 33806089496)
    (zero : state.globals.lookup (ofString "bls_c") = some (.val (.word 0)))
    (arena : ∀ address : BitVec 64, H.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 2 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "bls_consts_init") []) = (none,post) ∧
      post.clock = state.clock - 2 ∧ post.locals = state.locals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.memory = memWrites state.memory H blsConstsCells ∧
      post.globals = (state.globals.update (ofString "heap_ptr",.val (.word (H + 7136)))).update
        (ofString "bls_c",.val (.word H)) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have guard : evaluateHOLFiniteState entry
      (.ite (.cmp .notEqual (.var .global (ofString "bls_c")) (.const 0)) (.return (.const 0)) .skip) = (none,entry) := by
    rw [evaluateHOLFiniteState_ite]
    simp [entry,callEntryStateHOLFinite,evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  obtain ⟨ready,run,clock,memory,_,rcode,domain,globals,_⟩ := evaluate_globalAllocation_prefix entry
    [(ofString "bls_c",7136)] (globalConstantStores (ofString "bls_c") blsConstsCells (.return (.const 0))) H code heap
    (by simp; decide) (by simp; exact ⟨0,zero⟩)
    (by simpa using (allocationPlan_safe [7136] H (by simp; omega)).1) (by simp; change 1 ≤ state.clock - 1; omega)
  simp only [globalAllocationGlobals,List.length_cons,List.length_nil] at globals clock
  have finish := allocationEnd_aligned_exact H 7136 aligned (by decide) (by simp; omega)
  rw [finish] at globals
  have hc : ready.globals.lookup (ofString "bls_c") = some (.val (.word H)) := by
    rw [globals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have stores := evaluate_globalConstantStores ready (ofString "bls_c") H blsConstsCells (.return (.const 0)) hc
    (by
      intro cell member
      have bound := blsConstsCells_offset cell member
      rw [domain]
      apply arena
      · rw [BitVec.toNat_add_of_lt (by omega)]; omega
      · rw [BitVec.toNat_add_of_lt (by omega)]; omega)
  have body : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_bls_consts_init) =
      (some (.returned (.val (.word 0))),
        emptyLocalsHOLFinite {ready with memory := memWrites ready.memory H blsConstsCells}) := by
    rw [source_blsConstsInit_body,bnSeqNone guard,run,stores]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have lookup := pan_no_args_lookup state.code.lookup (ofString "bls_consts_init")
    (sourceFunctionBody Guest.guestFn_bls_consts_init) (by rw [code]; exact originalRuntimeCode_blsConstsInit_lookup)
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "bls_consts_init") [] []
    (sourceFunctionBody Guest.guestFn_bls_consts_init) HolFiniteMapExact.empty .one (.val (.word 0)) _
    rfl lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨_,call,?_,rfl,rcode,domain,?_,globals⟩
  · change ready.clock = state.clock - 2
    change ready.clock = state.clock - 1 - 1 at clock
    omega
  · change memWrites ready.memory H blsConstsCells = _
    rw [memory]
    rfl

/-- Repeated bls_consts_init (bls_c a nonzero word) returns at once: one tick. -/
theorem evaluate_blsConstsInit_call_installed {F : Type} (state : PanSemStateFiniteExact 64 F) (C : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (installed : state.globals.lookup (ofString "bls_c") = some (.val (.word C))) (nonzero : C ≠ 0)
    (budget : 1 ≤ state.clock) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "bls_consts_init") []) =
      (none,{state with clock := state.clock - 1}) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have condition : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
      (.cmp .notEqual (.var .global (ofString "bls_c")) (.const 0)) = some (.val (.word 1)) := by
    simp [entry,callEntryStateHOLFinite,evalHOLExact,installed,Compiler.Encoders.Asm.wordCmpHOL]
    simpa using nonzero
  have body : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_bls_consts_init) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite entry) := by
    rw [source_blsConstsInit_body,evaluateHOLFiniteState_seq_line780]
    simp only [evaluateHOLFiniteState_ite,condition]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have lookup := pan_no_args_lookup state.code.lookup (ofString "bls_consts_init")
    (sourceFunctionBody Guest.guestFn_bls_consts_init) (by rw [code]; exact originalRuntimeCode_blsConstsInit_lookup)
  rw [evaluateHOLFiniteState_call_return_caller_locals state none (ofString "bls_consts_init") [] []
    (sourceFunctionBody Guest.guestFn_bls_consts_init) HolFiniteMapExact.empty .one (.val (.word 0)) _
    rfl lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])]
  rfl

#print axioms evaluate_blsConstsInit_call_first
#print axioms evaluate_blsConstsInit_call_installed
end InitECandidate.Runtime
