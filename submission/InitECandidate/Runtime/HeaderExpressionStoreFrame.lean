import InitECandidate.Runtime.HeaderExpressionStoreReach
import InitECandidate.Runtime.HeaderWordStoreReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- An actual one-word expression store changes exactly its own destination address, so
any other word survives it; the store also keeps the locals, the domain, the code and the
globals, and costs no source clock. -/
theorem header_expression_store_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record value : BitVec 64) (offset : Nat) (expression : ExpHOL 64)
    (continuation : ProgHOL 64) (code : s.code = originalRuntimeCode)
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (atValue : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) expression = some (.val (.word value)))
    :
    Reaches s (.seq (headerExpressionStore expression offset) continuation)
      (fun post => post.locals = s.locals ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        (∀ global : MlS, post.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, address ≠ record + BitVec.ofNat 64 offset →
          post.memory address = s.memory address))
      0 continuation := by
  apply runBounded_seq_reaches s (headerExpressionStore expression offset) continuation _ 0
    (RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega))
  · intro v
    exact evaluate_noDirectReturn (headerExpressionStore expression offset) rfl s v
  · intro post normal
    have control := evaluate_store_control_frame s
      (.op .add [.var .local (ofString "h"),.const (BitVec.ofNat 64 offset)]) expression
    have metadata := evaluateHOLFiniteState_metadata s (headerExpressionStore expression offset)
    change evaluateHOLFiniteState s (.store _ _) = _ at normal
    rw [normal] at control
    change evaluateHOLFiniteState s (headerExpressionStore expression offset) = _ at normal
    rw [normal] at metadata
    have globals : (evaluateHOLFiniteState s (headerExpressionStore expression offset)).2.globals = s.globals := by
      unfold headerExpressionStore
      rw [evaluateHOLFiniteState_store]
      repeat' first | split | rfl
    rw [normal] at globals
    have memory : ∀ address : BitVec 64, address ≠ record + BitVec.ofNat 64 offset →
        post.memory address = s.memory address := by
      intro address different
      have frame := evaluate_wordStore_memory_frame s
        (.op .add [.var .local (ofString "h"),.const (BitVec.ofNat 64 offset)]) expression (record + BitVec.ofNat 64 offset) address
        (by simp [evalHOLExact,evalListHOLExact,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord])
        (by intro parsed ev; exact ⟨value,Option.some.inj (ev.symm.trans atValue)⟩)
        (by intro same; exact different same)
      change (evaluateHOLFiniteState s (headerExpressionStore expression offset)).2.memory address = s.memory address at frame
      rw [normal] at frame
      exact frame
    exact ⟨control.2.1,metadata.2.1,metadata.1,fun global => by rw [globals],memory⟩

#print axioms header_expression_store_frame
end InitECandidate.Runtime
