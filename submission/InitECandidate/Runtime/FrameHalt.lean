import InitECandidate.Runtime.GasFrameExpressions

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def fundingAddress (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [.var .global (ofString "ev"), .const offset]

noncomputable def sourceWriteWord {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (address value : BitVec 64) : PanSemStateFiniteExact 64 σ :=
  { state with memory := fun current => if current = address then .word value else state.memory current }

theorem eval_fundingAddress {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame offset : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame))) :
    @evalHOLExact 64 σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (fundingAddress offset) =
      some (.val (.word (frame + offset))) := by
  classical
  simp [fundingAddress, evalHOLExact, evalListHOLExact, toExact, hFrame,
    wordOpHOL, wordOp, valueIsWord, valueWord]

/-- Ordinary word-store equation specialized without changing the evaluator. -/
theorem evaluate_store_word {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (address value : BitVec 64) (destination expression : ExpHOL 64)
    (hAddress : @evalHOLExact 64 σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) destination =
        some (.val (.word address)))
    (hValue : @evalHOLExact 64 σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
        some (.val (.word value)))
    (domain : state.memaddrs address) :
    evaluateHOLFiniteState state (.store destination expression) =
      (none, sourceWriteWord state address value) := by
  classical
  rw [evaluateHOLFiniteState_store, hAddress, hValue]
  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, domain, sourceWriteWord]

theorem evaluate_seq_none {σ : Type} {state middle final : PanSemStateFiniteExact 64 σ}
    {first second : ProgHOL 64} {result : Option (PanSemResultExact 64)}
    (one : evaluateHOLFiniteState state first = (none, middle))
    (two : evaluateHOLFiniteState middle second = (result, final)) :
    evaluateHOLFiniteState state (.seq first second) = (result, final) := by
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  rw [fixClockHOLFinite_evaluateState, one]
  exact two

theorem source_frameHalt_body : sourceFunctionBody Guest.guestFn_frame_halt =
    .seq (.store (fundingAddress 184) frameHaltStoredUsed)
      (.seq (.store (fundingAddress 64) (.const 0))
        (.seq (.store (fundingAddress 160) (.var .local (ofString "err")))
          (.return (.const 0)))) := by cbv

noncomputable def frameHaltPost {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame left used error : BitVec 64) : PanSemStateFiniteExact 64 σ :=
  emptyLocalsHOLFinite (sourceWriteWord
    (sourceWriteWord (sourceWriteWord state (frame + 184) (used + left)) (frame + 64) 0)
    (frame + 160) error)

/-- Complete execution summary for the actual frame_halt source body, uniformly
at any clock. In particular it performs no recursive call or clock tick. -/
theorem evaluate_source_frameHalt {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame left used error : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hError : state.locals.lookup (ofString "err") = some (.val (.word error)))
    (leftDomain : state.memaddrs (frame + 64))
    (usedDomain : state.memaddrs (frame + 184))
    (errorDomain : state.memaddrs (frame + 160))
    (leftMemory : state.memory (frame + 64) = .word left)
    (usedMemory : state.memory (frame + 184) = .word used) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_frame_halt) =
      (some (.returned (.val (.word 0))), frameHaltPost state frame left used error) := by
  classical
  rw [source_frameHalt_body]
  let one := sourceWriteWord state (frame + 184) (used + left)
  let two := sourceWriteWord one (frame + 64) 0
  let three := sourceWriteWord two (frame + 160) error
  have first : evaluateHOLFiniteState state (.store (fundingAddress 184) frameHaltStoredUsed) =
      (none, one) := evaluate_store_word state (frame + 184) (used + left) _ _
        (eval_fundingAddress state frame 184 hFrame)
        (eval_frameHaltStoredUsed state frame left used hFrame leftDomain usedDomain leftMemory usedMemory)
        usedDomain
  have second : evaluateHOLFiniteState one (.store (fundingAddress 64) (.const 0)) =
      (none, two) := by
    apply evaluate_store_word
    · exact eval_fundingAddress one frame 64 hFrame
    · rfl
    · exact leftDomain
  have third : evaluateHOLFiniteState two
      (.store (fundingAddress 160) (.var .local (ofString "err"))) = (none, three) := by
    apply evaluate_store_word
    · exact eval_fundingAddress two frame 160 hFrame
    · exact hError
    · exact errorDomain
  have finish : evaluateHOLFiniteState three (.return (.const 0)) =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite three) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  exact evaluate_seq_none first (evaluate_seq_none second (evaluate_seq_none third finish))

/-- The concrete evaluator post-state implements the funding halt transition;
the three affected bookkeeping slots cannot alias at any 64-bit frame address. -/
theorem frameHaltPost_funding {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame left used spilled error : BitVec 64)
    (spillMemory : state.memory (frame + 192) = .word spilled) :
    (frameHaltPost state frame left used error).memory (frame + 64) = .word 0 ∧
    (frameHaltPost state frame left used error).memory (frame + 184) = .word (used + left) ∧
    (frameHaltPost state frame left used error).memory (frame + 192) = .word spilled := by
  simp [frameHaltPost, sourceWriteWord, emptyLocalsHOLFinite]
  exact spillMemory

/-- A memory-level frame funding invariant. This is tied to the three actual
source bookkeeping cells rather than an independent abstract counter. -/
def HasGasFunding {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame : BitVec 64) (funding : GasFunding) : Prop :=
  state.memory (frame + 64) = .word funding.left ∧
  state.memory (frame + 184) = .word funding.used ∧
  state.memory (frame + 192) = .word funding.spilled

/-- Actual source execution of frame_halt preserves the regular funding
potential, with every memory-access premise explicit. -/
theorem frameHalt_preserves_funding {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame error : BitVec 64) (funding : GasFunding)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hError : state.locals.lookup (ofString "err") = some (.val (.word error)))
    (leftDomain : state.memaddrs (frame + 64))
    (usedDomain : state.memaddrs (frame + 184))
    (errorDomain : state.memaddrs (frame + 160))
    (memory : HasGasFunding state frame funding)
    (budget : funding.potential ≤ 200000000) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_frame_halt) =
        (some (.returned (.val (.word 0))), post) ∧
      HasGasFunding post frame funding.halt ∧
      funding.halt.potential = funding.potential ∧ post.clock = state.clock := by
  refine ⟨frameHaltPost state frame funding.left funding.used error, ?_, ?_, ?_, rfl⟩
  · exact evaluate_source_frameHalt state frame funding.left funding.used error hFrame hError
      leftDomain usedDomain errorDomain memory.1 memory.2.1
  · exact frameHaltPost_funding state frame funding.left funding.used funding.spilled error memory.2.2
  · exact funding.halt_potential budget

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.evaluate_source_frameHalt

#print axioms InitECandidate.Runtime.frameHalt_preserves_funding
