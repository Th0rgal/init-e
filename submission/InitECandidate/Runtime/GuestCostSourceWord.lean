import InitECandidate.Runtime.GuestCostSourceLoopTop
import InitECandidate.Runtime.LoopWordPDefault
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect Flapjack.Compiler.Encoders.Asm
open InitE InitECandidate.Proofs.FrontendStages
variable {fn : Flapjack.Pancake.PanLang.MlS}

/-! The guest's source → Word transfer: the installed Loop entry of
`guest_source_loop`, compiled by `loop_to_word`, run from any Word state
related to it as in the pinned `compile_correct`, executes Word work at most
`sharpScore ev + 25061` under `loopWordPrice`. -/

/-- Guest source → Word executed work. -/
theorem guest_source_word (input : Guest.InputBlob) {C : Type} (W : Type)
    (target : WordSemStateFiniteExact 64 C Guest.HostMemory) (arch : AsmArchitecture) (clock : Nat)
    (hmem : ∀ address, (sourceInitialState input).memaddrs address →
      target.memory address = wlabWlocExact ((sourceInitialState input).memory address))
    (hnolabels : noLabelsHOL target.memory (fun address => target.mdomain address = true))
    (hmdomain : (fun address => target.mdomain address = true) =
      (fun address => (sourceInitialState input).memaddrs address ∨
        Compiler.Backend.StackRemove.addresses (sourceInitialState input).topAddr guestGlobalsSize address))
    {s1 : PanSemStateFiniteExact 64 Guest.HostMemory}
    (hs1 : @evaluateDeclsHOLFinite 64 Guest.HostMemory _ { sourceInitialState input with structs := [] }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      (Guest.guestAst.map declToHOL) = some s1)
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {ev : List WorkEvent}
    (run : StatementRun fn { s1 with clock := clock } (.call none (Flapjack.Basis.Pure.MlString.ofString "main") [])
      r post ev)
    (ok : r ≠ some .error) :
    let start := Flapjack.Basis.Pure.MlString.ofString "main"
    let G := initialGlobalState (sourceInitialState input) target guestGlobalsSize clock
    let panCode := compileTopExactHOL (panSimpDeclsHOL InitE.sourceDeclarations) start
    let crepState := crepStateHOL G panCode G.memory
    let loopState := loopStateHOL crepState arch (compileProgDeclsHOLW panCode) target.clock target.memory
    let program := crepSimpProgHOL (compileProgExactHOLW (entryPanContext panCode) (.call none start []))
    let loopProgram := compileHOLExact (entryLoopContext arch panCode) .ln program
    ∃ T, @evaluateDeclsHOLFinite 64 Guest.HostMemory _ { G with structs := [] }
        (fun a => Classical.propDecidable (G.memaddrs a)) panCode = some T ∧
      ∃ extra, ∀ (t : WordSemStateFiniteExact 64 W Guest.HostMemory) (ctxt : Spt Nat) (retv : WordLocW 64)
        (labels : Nat × Nat),
        loopToWordStateRelHOLExact { loopState with clock := T.clock + 1 + extra } t →
        LoopToWord.localsRelHOL ctxt loopState.locals t.locals →
        sptLookup 0 t.locals = some retv → goodDimindex 64 → ¬ wordSemIsWordLoc retv = true →
        (∀ k, sptMem k (accVarsHOL loopProgram .ln) → sptMem k ctxt) →
        wordExecutionCost loopWordPrice (LoopToWord.compHOL ctxt loopProgram labels).1 t ≤ sharpScore ev + 25061 := by
  intro start G panCode crepState loopState program loopProgram
  obtain ⟨T, hT, extra, wl, work, bound, -, loopOk⟩ :=
    guest_source_loop input target arch clock hmem hnolabels hmdomain hs1 run ok
  refine ⟨T, hT, extra, fun t ctxt retv labels rel locals ret dim notWord acc => ?_⟩
  exact Nat.le_trans (loop_to_word_cost (C := W) work loopOk t ctxt retv labels rel locals ret dim notWord acc)
    bound

#print axioms guest_source_word
end InitECandidate.Runtime.FineCost
