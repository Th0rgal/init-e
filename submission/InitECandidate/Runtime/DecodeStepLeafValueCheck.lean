import InitECandidate.Runtime.DecodeStepLeafConstruction
import InitECandidate.Runtime.MptFailCallBound
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepLeafValueContinuation : ProgHOL 64 :=
  match decodeStepLeafBranch with
  | .decCall _ _ _ _ body => body
  | _ => .skip

theorem source_decodeStep_leaf_value_continuation : decodeStepLeafValueContinuation =
    .seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "vi"))) (.const 0))
      (.call (some (none,none)) (ofString "mpt_fail") [.const 6]) .skip) decodeStepLeafConstruction := by
  simp only [decodeStepLeafValueContinuation,decodeStepLeafConstruction,decodeStepLeafBranch,
    decodeStepCompactContinuation,decodeStepCompactCall,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A byte-string value passes the original type check and produces a leaf
with the certified path, layout and registry in two source ticks. -/
theorem evaluate_decodeStep_leaf_value_continuation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (leaf pointer length nibs count flag valuePointer valueLength consumed : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (pathLocal : state.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word flag)]))
    (valueLocal : state.locals.lookup (ofString "vi") = some
      (.rStruct [.val (.word (0 : BitVec 64)),.val (.word valuePointer),.val (.word valueLength),.val (.word consumed)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word leaf)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (budget : leaf.toNat + 64 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (registry : TrieWalkRegistry live extensions branches state)
    (layout : TrieNodeLayout live extensions branches size)
    (frontier : ∀ node ∈ live, node.toNat + size node ≤ leaf.toNat)
    (path : TrieNibbleRange state nibs count)
    (aligned : nibs.toNat % 8 = 0)
    (pathBefore : nibs.toNat + count.toNat ≤ leaf.toNat) :
    ∃ post, evaluateHOLFiniteState state decodeStepLeafValueContinuation =
        (some (.returned (.rStruct [.val (.word (0 : BitVec 64)),.val (.word leaf)])),post) ∧
      post.clock = state.clock - 2 ∧ TrieNibbleRange post nibs count ∧
      TrieWalkRegistry (insert leaf live) extensions branches post ∧
      TrieNodeLayout (insert leaf live) extensions branches (trieRecordSizeInsert size leaf 64) := by
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "vi"))) (.const 0))
        (.call (some (none,none)) (ofString "mpt_fail") [.const 6]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,valueLocal,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  obtain ⟨post,run,clock,valid,registered,allocated⟩ :=
    evaluate_decodeStep_leaf_construction state live extensions branches size
      leaf pointer length nibs count flag valuePointer valueLength 0 consumed pointerLocal lengthLocal pathLocal
      valueLocal heap code ticks budget heapDomain registry layout frontier path aligned pathBefore
  refine ⟨post,?_,clock,valid,registered,allocated⟩
  rw [source_decodeStep_leaf_value_continuation,evaluateHOLFiniteState_seq_line780,check]
  exact run

/-- A list-valued leaf payload takes mpt_fail(6), before any node allocation. -/
theorem evaluate_decodeStep_leaf_value_error {F : Type} (state : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed : BitVec 64)
    (nonzero : kind ≠ 0)
    (valueLocal : state.locals.lookup (ofString "vi") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state decodeStepLeafValueContinuation
    evaluated.2.clock = state.clock - 1 ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none ∧
      (∀ value, evaluated.1 ≠ some (.returned value)) := by
  have bound := evaluate_mptFail_call_bounded state (.const 6) 6 code (by omega) (by rfl)
  have noReturn := evaluate_discard_call_no_return state (ofString "mpt_fail") [.const 6]
  have notZero : kind ≠ BitVec.ofNat 64 0 := nonzero
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "vi"))) (.const 0))
        (.call (some (none,none)) (ofString "mpt_fail") [.const 6]) .skip) =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [.const 6]) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,valueLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero]
  rw [source_decodeStep_leaf_value_continuation,evaluateHOLFiniteState_seq_line780,check]
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [.const 6]) with
  | mk result post =>
    rw [run] at bound noReturn
    dsimp only at bound noReturn
    cases result with
    | none => exact False.elim (bound.2.2 rfl)
    | some stopped => exact ⟨bound.1,bound.2.1,bound.2.2,noReturn⟩

#print axioms evaluate_decodeStep_leaf_value_continuation
#print axioms evaluate_decodeStep_leaf_value_error
end InitECandidate.Runtime
