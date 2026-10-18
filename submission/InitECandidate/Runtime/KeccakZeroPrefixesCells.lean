import InitECandidate.Runtime.KeccakZeroPrefixes
import InitECandidate.Runtime.MemzeroAlignedCallCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- The actual state-buffer zeroing prefix reaches its original continuation
within 201 source ticks, preserving globals and caller locals. -/
theorem evaluate_keccak_state_zero_prefix_cells {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (binding : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 201 ≤ state.clock)
    (small : pointer.toNat + 200 ≤ 33806089496) (aligned : pointer.toNat % 8 = 0)
    (bytes : ∀ offset : Nat, offset < 200 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_keccak256)) = evaluateHOLFiniteState post (stateInitSpineDrop 2 (sourceFunctionBody Guest.guestFn_keccak256)) ∧
      ZeroBytePrefix post pointer 200 ∧ state.clock ≤ post.clock + 201 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.locals = state.locals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "stp"),.const 200] = some [.val (.word pointer),.val (.word (200 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,binding]
  obtain ⟨post,run,zero,cost,remaining,globals,postCode,domain,endian,locals,_⟩ := evaluate_memzero_aligned_call_cells state _ _ pointer 200
    args code ticks small aligned bytes
  refine ⟨post,?_,zero,cost,remaining,globals,locals,postCode,domain,endian⟩
  rw [source_keccak_state_zero_prefix,evaluateHOLFiniteState_seq_line780,run]

/-- The actual pad-buffer zeroing prefix reaches its original continuation
within 137 source ticks, preserving globals and caller locals. -/
theorem evaluate_keccak_pad_zero_prefix_cells {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (binding : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 137 ≤ state.clock)
    (small : pointer.toNat + 136 ≤ 33806089496) (aligned : pointer.toNat % 8 = 0)
    (bytes : ∀ offset : Nat, offset < 136 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (keccakRemainderTail) = evaluateHOLFiniteState post (keccakAfterPadZero) ∧
      ZeroBytePrefix post pointer 136 ∧ state.clock ≤ post.clock + 137 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.locals = state.locals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .global (ofString "keccak_pad"),.const 136] = some [.val (.word pointer),.val (.word (136 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,binding]
  obtain ⟨post,run,zero,cost,remaining,globals,postCode,domain,endian,locals,_⟩ := evaluate_memzero_aligned_call_cells state _ _ pointer 136
    args code ticks small aligned bytes
  refine ⟨post,?_,zero,cost,remaining,globals,locals,postCode,domain,endian⟩
  rw [source_keccak_pad_zero_prefix,evaluateHOLFiniteState_seq_line780,run]

#print axioms evaluate_keccak_state_zero_prefix_cells
#print axioms evaluate_keccak_pad_zero_prefix_cells
end InitECandidate.Runtime
