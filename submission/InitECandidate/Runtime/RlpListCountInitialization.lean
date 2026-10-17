import InitECandidate.Runtime.RlpListCountLoopBound
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpListCountLoopAndReturn : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_list_count with | .dec _ _ _ (.dec _ _ _ body) => body | _ => .skip

theorem source_rlpListCount_initialization : sourceFunctionBody Guest.guestFn_rlp_list_count =
    .dec (ofString "count") .one (.const 0) (.dec (ofString "off") .one (.const 0) rlpListCountLoopAndReturn) := by
  simp only [rlpListCountLoopAndReturn,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpListCount_loop_and_return : rlpListCountLoopAndReturn =
    .seq rlpListCountLoop (.return (.var .local (ofString "count"))) := by
  simp only [rlpListCountLoopAndReturn,rlpListCountLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

noncomputable def rlpListCountInitialState {F : Type} (state : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "off") (.val (.word 0)) (setVarHOLFinite (ofString "count") (.val (.word 0)) state)

/-- Actual count/offset initialization establishes the full loop witness with
zero count and zero consumed input, leaving the clock and arena untouched. -/
theorem rlpListCount_initial_witness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address) :
    ∃ valid : RlpListCountLoopWitness (rlpListCountInitialState state) pointer length scratch frame ceiling,
      valid.offset = 0 ∧ valid.count = 0 := by
  refine ⟨{
    offset := 0, count := 0, pointerLocal := ?_, lengthLocal := ?_, offsetLocal := ?_, countLocal := ?_
    countBound := Nat.le_refl _, offsetBound := Nat.zero_le _, scratchGlobal := scratchGlobal, frameGlobal := frameGlobal
    code := code, arena := arena },rfl,rfl⟩
  · simpa [rlpListCountInitialState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "p" by decide,show ofString "count" ≠ ofString "p" by decide] using pointerLocal
  · simpa [rlpListCountInitialState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "len" by decide,show ofString "count" ≠ ofString "len" by decide] using lengthLocal
  · simp [rlpListCountInitialState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [rlpListCountInitialState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "count" by decide]

/-- Inverting the original two initializer scopes retains the loop result,
clock and globals across restoration of the caller's count/offset bindings. -/
theorem evaluate_rlpListCount_initialized_loop {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_count) = (result,post)) :
    ∃ output, evaluateHOLFiniteState (rlpListCountInitialState state) rlpListCountLoopAndReturn = (result,output) ∧
      post.clock = output.clock ∧ post.globals = output.globals := by
  rw [source_rlpListCount_initialization] at run
  obtain ⟨first,firstRun,restore1⟩ := evaluate_dec_word_result_scope state post (ofString "count") (.const 0) 0 _ result (by rfl) run
  obtain ⟨output,bodyRun,restore2⟩ := evaluate_dec_word_result_scope _ first (ofString "off") (.const 0) 0 _ result (by rfl) firstRun
  refine ⟨output,bodyRun,?_,?_⟩
  · rw [restore1,restore2]
  · rw [restore1,restore2]

#print axioms rlpListCount_initial_witness
#print axioms evaluate_rlpListCount_initialized_loop
end InitECandidate.Runtime
