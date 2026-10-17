import InitECandidate.Runtime.RlpItemLongOuterTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemAfterLongString : ProgHOL 64 :=
  match rlpItemAfterShortString with
  | .seq _ body => body
  | _ => .skip

theorem source_rlpItem_long_dispatch : rlpItemAfterShortString =
    .seq (.ite (.cmp .notLower (.const 191) (.var .local (ofString "b"))) rlpItemLongString .skip)
      rlpItemAfterLongString := by
  simp only [rlpItemAfterLongString,rlpItemLongString,rlpItemAfterShortString,rlpItemAfterSingleByte,
    rlpItemAfterByte,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original header comparisons select the long-string case, whose
terminal result prevents all later list parsing. No payload readability is assumed. -/
theorem evaluate_rlpItem_long_after_load_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpItemAfterByte = (result,post) ∧
      state.clock ≤ post.clock + 11 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none := by
  have first : evaluateHOLFiniteState state
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
        (.return (.rstruct [.const 0,.var .local (ofString "p"),.const 1,.const 1])) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat < 128 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside,evaluateHOLFiniteState_skip]
  have second : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 183) (.var .local (ofString "b"))) rlpItemShortString .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 183 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 191) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,upper]
  obtain ⟨result,post,run,cost,remaining,noTimeout⟩ := evaluate_rlpItem_long_string_bounded state pointer header
    pointerLocal headerLocal lower upper code ticks
  have terminal := evaluate_rlpItem_long_string_terminal state pointer header pointerLocal headerLocal lower upper code ticks
  rw [run] at terminal
  rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,first]
  dsimp only
  rw [source_rlpItem_short_dispatch,evaluateHOLFiniteState_seq_line780,second]
  dsimp only
  rw [source_rlpItem_long_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  rw [run]
  cases result with
  | none => exact False.elim (terminal rfl)
  | some stopped => exact ⟨some stopped,post,rfl,cost,remaining,noTimeout,terminal⟩

#print axioms evaluate_rlpItem_long_after_load_bounded
end InitECandidate.Runtime
