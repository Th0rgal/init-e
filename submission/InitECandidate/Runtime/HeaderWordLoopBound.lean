import InitECandidate.Runtime.RankedWhile
import InitECandidate.Runtime.NoLoopControl
import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.StatelessInputSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def headerWordAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_hdr_word_field)
def headerWordLoopCondition : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "j")) (.rfield 1 (.var .local (ofString "f")))
def headerWordLoopBody : ProgHOL 64 :=
  .seq (.assign .local (ofString "v") (.op .or [
    .shift .lsl (.var .local (ofString "v")) (.const 8),
    .loadByte (.op .add [.rfield 0 (.var .local (ofString "f")),.var .local (ofString "j")])]))
    (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"),.const 1]))
def headerWordLoop : ProgHOL 64 := .while headerWordLoopCondition headerWordLoopBody

theorem source_header_word_loop : headerWordAt 4 =
    .seq headerWordLoop (.return (.var .local (ofString "v"))) := rfl

def HeaderWordRank (pointer length : BitVec 64) {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ∃ j : BitVec 64, s.locals.lookup (ofString "j") = some (.val (.word j)) ∧
    s.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]) ∧
    j.toNat ≤ length.toNat ∧ length.toNat ≤ 8 ∧ rank = length.toNat - j.toNat

theorem header_word_body_counted : CountedBody (ofString "j") 1 headerWordLoopBody 0 := by
  exact CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr

theorem eval_header_word_loop_condition {F : Type} (s : PanSemStateFiniteExact 64 F) (pointer length j : BitVec 64)
    (atJ : s.locals.lookup (ofString "j") = some (.val (.word j)))
    (atField : s.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)])) :
    evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) headerWordLoopCondition =
      some (.val (.word (if j.toNat < length.toNat then 1 else 0))) := by
  simp [evalHOLFinite_eq_toExact,headerWordLoopCondition,evalHOLExact,atJ,atField,
    Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

/-- The original byte accumulation loop is ranked by remaining bytes. Failed
byte reads also obey the bound; no input readability or successful run is assumed. -/
theorem header_word_loop_ranked (pointer length : BitVec 64) :
    ∀ rank : Nat, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      HeaderWordRank pointer length s rank → rank ≤ s.clock →
      RankedOutcome s headerWordLoopCondition rank (HeaderWordRank pointer length) False
        (evaluateHOLFiniteState s headerWordLoop) := by
  have exit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), HeaderWordRank pointer length s 0 →
      ∀ w : BitVec 64, evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) headerWordLoopCondition =
        some (.val (.word w)) → w = 0 := by
    intro F s ⟨j,atJ,atField,below,small,ranking⟩ w evaluated
    rw [eval_header_word_loop_condition s pointer length j atJ atField] at evaluated
    have stopped : ¬ j.toNat < length.toNat := by omega
    simpa [stopped] using evaluated.symm
  have step : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat) (w : BitVec 64),
      s.code = originalRuntimeCode → HeaderWordRank pointer length s (rank + 1) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) headerWordLoopCondition = some (.val (.word w)) →
      w ≠ 0 → 0 + 1 ≤ s.clock →
      s.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite s) headerWordLoopBody).2.clock + 0 ∧
      (evaluateHOLFiniteState (decClockHOLFinite s) headerWordLoopBody).2.clock ≤ s.clock - 1 ∧
      (evaluateHOLFiniteState (decClockHOLFinite s) headerWordLoopBody).1 ≠ some .timeOut ∧
      ((evaluateHOLFiniteState (decClockHOLFinite s) headerWordLoopBody).1 = none ∨
          (evaluateHOLFiniteState (decClockHOLFinite s) headerWordLoopBody).1 = some .continue →
        ∃ m, m ≤ rank ∧ HeaderWordRank pointer length (evaluateHOLFiniteState (decClockHOLFinite s) headerWordLoopBody).2 m ∧
          (evaluateHOLFiniteState (decClockHOLFinite s) headerWordLoopBody).2.code = s.code) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite s) headerWordLoopBody).1 = some .break → False ∧
        ∃ m, HeaderWordRank pointer length (evaluateHOLFiniteState (decClockHOLFinite s) headerWordLoopBody).2 m ∧
          (evaluateHOLFiniteState (decClockHOLFinite s) headerWordLoopBody).2.code = s.code) := by
    intro F s rank w code ⟨j,atJ,atField,below,small,ranking⟩ _ _ _
    have body := header_word_body_counted.run (decClockHOLFinite s) code j atJ (by omega)
    have control := evaluate_noLoopControl headerWordLoopBody rfl (decClockHOLFinite s)
    refine ⟨body.1,body.2.1,body.2.2.1,?_,fun h => (control.1 h).elim⟩
    intro normalOrContinue
    have normal := normalOrContinue.resolve_right control.2
    obtain ⟨nextJ,nextCode⟩ := body.2.2.2.2 normal
    have fieldKept := evaluate_avoidsLocal_flowing (ofString "f") headerWordLoopBody rfl
      (decClockHOLFinite s) (Or.inl normal)
    have increment : (j + (1#64)).toNat = j.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change j.toNat + 1 < 2^64; omega)]; rfl
    refine ⟨length.toNat - (j + (1#64)).toNat,(by rw [increment]; omega),?_,nextCode⟩
    exact ⟨j + (1#64),nextJ,fieldKept.trans atField,(by rw [increment]; omega),small,rfl⟩
  intro rank F s code valid budget
  simpa only [Nat.zero_add,Nat.mul_one,headerWordLoop] using
    rankedWhile_run headerWordLoopCondition headerWordLoopBody 0 (HeaderWordRank pointer length) False
      exit step rank s code valid (by simpa using budget)

/-- At most eight source-loop ticks after the accepted field-size guard. -/
theorem runBounded_header_word_loop {F : Type} (s : PanSemStateFiniteExact 64 F) (pointer length j : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atJ : s.locals.lookup (ofString "j") = some (.val (.word j)))
    (atField : s.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (below : j.toNat ≤ length.toNat) (small : length.toNat ≤ 8) (budget : 8 ≤ s.clock) :
    RunBounded s headerWordLoop 8 := by
  obtain ⟨spent,kept,safe,_⟩ := header_word_loop_ranked pointer length (length.toNat - j.toNat) s code
    ⟨j,atJ,atField,below,small,rfl⟩ (by omega)
  exact ⟨by omega,kept,safe⟩

#print axioms source_header_word_loop
#print axioms header_word_body_counted
#print axioms header_word_loop_ranked
#print axioms runBounded_header_word_loop
end InitECandidate.Runtime
