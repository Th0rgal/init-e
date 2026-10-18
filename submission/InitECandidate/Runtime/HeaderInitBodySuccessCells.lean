import InitECandidate.Runtime.HeaderInitBodySuccess
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_headerInit_body_success_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "hdr_zero8") = some (.val (.word 0)))
    (aligned : pointer.toNat % 8 = 0) (room : pointer.toNat + 8 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → pointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 10 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_header_init) =
        (some (.returned (.val (.word 0))),post) ∧
      state.clock ≤ post.clock + 10 ∧ post.clock ≤ state.clock ∧ ZeroBytePrefix post pointer 8 ∧
      post.locals = HolFiniteMapExact.empty ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals.lookup (ofString "hdr_zero8") = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 8))) ∧
      (∀ key, key ≠ ofString "hdr_zero8" → key ≠ ofString "heap_ptr" →
        post.globals.lookup key = state.globals.lookup key) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .notEqual (.var .global (ofString "hdr_zero8")) (.const 0)) = some (.val (.word 0)) := by
    simp [evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.const 8] = some [.val (.word 8)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  have finish := allocationEnd_aligned_toNat pointer 8 room aligned (by decide)
  obtain ⟨allocated,allocation,clock,_,_,installed,domain,_,atHeader,atHeap,other⟩ :=
    evaluate_alloc_global_call state (.const 8) pointer 8 0 (ofString "hdr_zero8") args code (by omega) heap zero
      (by decide) (allocationGuard_of_sum_bound pointer 8 room) (by rw [finish]; exact room)
  have domains := aligned_interval_byte_domains allocated pointer 8 aligned (by omega)
    (by intro address cellAligned lower upper; rw [domain]; apply arena address cellAligned lower; change address.toNat < pointer.toNat + 8 at upper; omega)
  have zeroArgs : evalListHOLFinite allocated (h := fun a => Classical.propDecidable (allocated.memaddrs a))
      [.var .global (ofString "hdr_zero8"),.const 8] = some [.val (.word pointer),.val (.word 8)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atHeader]
  obtain ⟨cleared,clearRun,covered,cost,remaining,globals,postCode,addresses,_,_,_⟩ :=
    evaluate_memzero_aligned_call_cells allocated (.var .global (ofString "hdr_zero8")) (.const 8) pointer 8 zeroArgs
      (installed.trans code) (by change 9 ≤ allocated.clock; omega) room aligned domains
  refine ⟨emptyLocalsHOLFinite cleared,?_,?_,?_,covered,rfl,postCode.trans installed,addresses.trans domain,?_,?_,?_⟩
  · rw [source_headerInit_body,evaluateHOLFiniteState_seq_line780]
    simp only [evaluateHOLFiniteState_ite,condition,if_true,evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780,allocation]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,clearRun]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  · change state.clock ≤ cleared.clock + 10
    change allocated.clock ≤ cleared.clock + 8 + 1 at cost
    omega
  · change cleared.clock ≤ state.clock
    omega
  · change cleared.globals.lookup _ = _
    rw [globals]
    exact atHeader
  · change cleared.globals.lookup _ = _
    rw [globals]
    exact atHeap
  · intro key different notHeap
    change cleared.globals.lookup key = _
    rw [globals]
    exact other key different notHeap

#print axioms evaluate_headerInit_body_success_cells
end InitECandidate.Runtime
