import InitECandidate.Runtime.DecodeStepExtensionRecordArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original non-leaf continuation, including its empty-path
check and scratch record creation, costs one source tick and retains the path. -/
theorem evaluate_decodeStep_extension_continuation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (scratch frame arr pointer length nibs count : BitVec 64)
    (arrLocal : state.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (pathLocal : state.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word (0 : BitVec 64))]))
    (nonempty : 0 < count.toNat)
    (valid : TrieNibbleRange state nibs count)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (request : (88 : BitVec 64) ≤ scratch - frame)
    (within : frame ≤ scratchAllocationEnd scratch 88)
    (fits : 88 ≤ scratch.toNat)
    (below : scratch.toNat ≤ nibs.toNat)
    (aligned : nibs.toNat % 8 = 0)
    (bounded : nibs.toNat + count.toNat ≤ 2^64)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state decodeStepCompactContinuation =
        (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word (scratchAllocationEnd scratch 88))])),post) ∧
      post.clock = state.clock - 1 ∧ TrieNibbleRange post nibs count ∧
      post.memory (scratchAllocationEnd scratch 88 + 64) = .word nibs ∧
      post.memory (scratchAllocationEnd scratch 88 + 72) = .word count := by
  obtain ⟨post,recordRun,clock,path,pointerField,countField⟩ :=
    evaluate_decodeStep_extension_record_arena state scratch frame arr pointer length nibs count 0
      arrLocal pointerLocal lengthLocal pathLocal valid code ticks scratchGlobal frameGlobal request within
      fits below aligned bounded arena
  have notZero : count ≠ BitVec.ofNat 64 0 := by
    intro equal
    have same := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat,Nat.zero_mod] at same
    omega
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.rfield 1 (.var .local (ofString "cn"))) (.const 0))
        (.call (some (none,none)) (ofString "mpt_fail") [.const 7]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,pathLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  refine ⟨post,?_,clock,path,pointerField,countField⟩
  rw [evaluate_decodeStep_extension_dispatch state nibs count pathLocal,
    source_decodeStep_extension_suffix,evaluateHOLFiniteState_seq_line780,check]
  exact recordRun

/-- The complementary empty extension path terminates in mpt_fail(7),
without allocating a continuation record or returning a node. -/
theorem evaluate_decodeStep_empty_extension {F : Type} (state : PanSemStateFiniteExact 64 F)
    (nibs : BitVec 64)
    (pathLocal : state.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word (0 : BitVec 64)),.val (.word (0 : BitVec 64))]))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state decodeStepCompactContinuation
    evaluated.2.clock = state.clock - 1 ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none ∧
      (∀ value, evaluated.1 ≠ some (.returned value)) := by
  have bound := evaluate_mptFail_call_bounded state (.const 7) 7 code (by omega) (by rfl)
  have noReturn := evaluate_discard_call_no_return state (ofString "mpt_fail") [.const 7]
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.rfield 1 (.var .local (ofString "cn"))) (.const 0))
        (.call (some (none,none)) (ofString "mpt_fail") [.const 7]) .skip) =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [.const 7]) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,pathLocal,Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluate_decodeStep_extension_dispatch state nibs 0 pathLocal,
    source_decodeStep_extension_suffix,evaluateHOLFiniteState_seq_line780,check]
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [.const 7]) with
  | mk result post =>
    rw [run] at bound noReturn
    dsimp only at bound noReturn
    cases result with
    | none => exact False.elim (bound.2.2 rfl)
    | some stopped => exact ⟨bound.1,bound.2.1,bound.2.2,noReturn⟩

#print axioms evaluate_decodeStep_empty_extension
#print axioms evaluate_decodeStep_extension_continuation
end InitECandidate.Runtime
