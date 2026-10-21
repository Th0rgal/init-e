import InitECandidate.Runtime.SourceCostLoopControl
import InitECandidate.Runtime.SourceCostLoopPrice
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-! Two Loop pricings of Crep work. `sharpPricing` charges each Crep expression
its exact context-free Loop price (`loopNodePrice`) and native units per
statement; the Crep-to-Loop transfer then has factor one. `coarsePricing`
recovers the earlier uniform `7 *` statement for node-count `CrepWork`. -/

/-- Exact Loop prices: expression code and value work, one move per argument,
two units per statement. -/
def sharpPricing : LoopPricing where
  price := loopNodePrice
  priceList := sharpCrepList
  unit := 37
  prim := 85
  call := 240
  ret := 49
  exprOk := fun context tmp live e => crep_to_loop_price_work context tmp live e
  listOk := fun context tmp live es => by
    obtain ⟨cost, h, b⟩ := crep_to_loop_price_list_work context tmp live es
    have len := loopCompileExps_length context es tmp live
    exact ⟨cost, h, by simp only [sharpCrepList]; (try simp only [] at b len ⊢); omega⟩
  unitOk := by decide
  primOk := by decide
  callOk := by decide
  retOk := by decide

/-- Crep work at exact Loop prices. -/
abbrev CrepWorkS {σ : Type} := @CrepWorkP loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.skip {σ : Type} := @CrepWorkP.skip loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.tick {σ : Type} := @CrepWorkP.tick loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.breakStmt {σ : Type} := @CrepWorkP.breakStmt loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.continueStmt {σ : Type} := @CrepWorkP.continueStmt loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.raise {σ : Type} := @CrepWorkP.raise loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.assign {σ : Type} := @CrepWorkP.assign loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.storeGlob {σ : Type} := @CrepWorkP.storeGlob loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.store {σ : Type} := @CrepWorkP.store loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.store32 {σ : Type} := @CrepWorkP.store32 loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.storeByte {σ : Type} := @CrepWorkP.storeByte loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.returnStmt {σ : Type} := @CrepWorkP.returnStmt loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.primitive {σ : Type} := @CrepWorkP.primitive loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.shMem {σ : Type} := @CrepWorkP.shMem loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.extCall {σ : Type} := @CrepWorkP.extCall loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.decFailure {σ : Type} := @CrepWorkP.decFailure loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.dec {σ : Type} := @CrepWorkP.dec loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.seqNext {σ : Type} := @CrepWorkP.seqNext loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.seqStop {σ : Type} := @CrepWorkP.seqStop loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.iteBranch {σ : Type} := @CrepWorkP.iteBranch loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.iteInvalid {σ : Type} := @CrepWorkP.iteInvalid loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.whileExit {σ : Type} := @CrepWorkP.whileExit loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.whileTimeout {σ : Type} := @CrepWorkP.whileTimeout loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.whileLoop {σ : Type} := @CrepWorkP.whileLoop loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.whileStop {σ : Type} := @CrepWorkP.whileStop loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.callShort {σ : Type} := @CrepWorkP.callShort loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.callBody {σ : Type} := @CrepWorkP.callBody loopNodePrice sharpCrepList 37 85 240 49 σ
abbrev CrepWorkS.callHandler {σ : Type} := @CrepWorkP.callHandler loopNodePrice sharpCrepList 37 85 240 49 σ

/-- Uniform node-count ceilings: six Loop units per Crep node, one more per
argument, seven per statement. -/
def coarsePricing : LoopPricing where
  price := fun e => 160 * crepNodeWork e
  priceList := fun es => 160 * crepListWork es
  unit := 200
  prim := 200
  call := 600
  ret := 49
  exprOk := fun context tmp live e => by
    obtain ⟨cost, h, b⟩ := crep_to_loop_local_work context tmp live e
    exact ⟨cost, h, by omega⟩
  listOk := fun context tmp live es => by
    obtain ⟨cost, h, b⟩ := crep_to_loop_list_work context tmp live es
    have len := loopCompileExps_length context es tmp live
    have ge := crepListWork_ge_length es
    exact ⟨cost, h, by (try simp only [] at b len ⊢); omega⟩
  unitOk := by decide
  primOk := by decide
  callOk := by decide
  retOk := by decide

/-- Node-count Crep work is coarse-priced Crep work up to the factor 200. -/
theorem crepWork_coarse {σ : Type} {t : CrepSemHOLState 64 σ} {p : CrepProgHOL 64} {w : Nat}
    (work : CrepWork t p w) : ∃ w', CrepWorkL coarsePricing t p w' ∧ w' ≤ 200 * w := by
  induction work with
  | skip t => exact ⟨_, .skip t, by simp [coarsePricing]⟩
  | tick t => exact ⟨_, .tick t, by simp [coarsePricing]⟩
  | breakStmt t label => exact ⟨_, .breakStmt t label, by simp [coarsePricing]⟩
  | continueStmt t label => exact ⟨_, .continueStmt t label, by simp [coarsePricing]⟩
  | raise t code => exact ⟨_, .raise t code, by simp [coarsePricing]⟩
  | assign t name value => exact ⟨_, .assign t name value, by simp only [coarsePricing]; omega⟩
  | storeGlob t address value => exact ⟨_, .storeGlob t address value, by simp only [coarsePricing]; omega⟩
  | store t address value => exact ⟨_, .store t address value, by simp only [coarsePricing]; omega⟩
  | store32 t address value => exact ⟨_, .store32 t address value, by simp only [coarsePricing]; omega⟩
  | storeByte t address value => exact ⟨_, .storeByte t address value, by simp only [coarsePricing]; omega⟩
  | returnStmt t values => exact ⟨_, .returnStmt t values, by simp only [coarsePricing]; omega⟩
  | primitive t names operator args =>
    exact ⟨_, .primitive t names operator args, by simp only [coarsePricing]; omega⟩
  | shMem t operator name address =>
    exact ⟨_, .shMem t operator name address, by simp only [coarsePricing]; omega⟩
  | extCall t function configuration configurationLength array arrayLength =>
    exact ⟨_, .extCall t function configuration configurationLength array arrayLength,
      by simp [coarsePricing]⟩
  | decFailure failed => exact ⟨_, .decFailure failed, by simp only [coarsePricing]; omega⟩
  | dec evaluated bodyRun ih =>
    obtain ⟨w', r', b'⟩ := ih
    exact ⟨_, .dec evaluated r', by simp only [coarsePricing]; omega⟩
  | seqNext one run two ihOne ihTwo =>
    obtain ⟨w1, r1, b1⟩ := ihOne
    obtain ⟨w2, r2, b2⟩ := ihTwo
    exact ⟨_, .seqNext r1 run r2, by omega⟩
  | seqStop one run ihOne =>
    obtain ⟨w1, r1, b1⟩ := ihOne
    exact ⟨_, .seqStop r1 run, by omega⟩
  | iteBranch guard branch ih =>
    obtain ⟨w', r', b'⟩ := ih
    exact ⟨_, .iteBranch guard r', by simp only [coarsePricing]; omega⟩
  | iteInvalid invalid => exact ⟨_, .iteInvalid invalid, by simp only [coarsePricing]; omega⟩
  | whileExit exit => exact ⟨_, .whileExit exit, by simp only [coarsePricing]; omega⟩
  | whileTimeout guard nonzero clock =>
    exact ⟨_, .whileTimeout guard nonzero clock, by simp only [coarsePricing]; omega⟩
  | whileLoop guard nonzero clock one run again rest ihOne ihRest =>
    obtain ⟨w1, r1, b1⟩ := ihOne
    obtain ⟨w2, r2, b2⟩ := ihRest
    exact ⟨_, .whileLoop guard nonzero clock r1 run again r2, by simp only [coarsePricing]; omega⟩
  | whileStop guard nonzero clock one run stop ihOne =>
    obtain ⟨w1, r1, b1⟩ := ihOne
    exact ⟨_, .whileStop guard nonzero clock r1 run stop, by simp only [coarsePricing]; omega⟩
  | callShort short => exact ⟨_, .callShort short, by simp only [coarsePricing]; omega⟩
  | callBody args lookup names clock bodyRun run unhandled ihBody =>
    obtain ⟨w1, r1, b1⟩ := ihBody
    exact ⟨_, .callBody args lookup names clock r1 run unhandled, by
      simp only [coarsePricing]; omega⟩
  | callHandler args lookup names clock bodyRun run handlerRun ihBody ihHandler =>
    obtain ⟨w1, r1, b1⟩ := ihBody
    obtain ⟨w2, r2, b2⟩ := ihHandler
    exact ⟨_, .callHandler args lookup names clock r1 run r2, by simp only [coarsePricing]; omega⟩

theorem LoopPaid.mono {F : Type} {context : CrepToLoopContextExact} {live : NumSet}
    {t : CrepSemHOLState 64 F} {u : LoopSemStateFiniteExact 64 F} {p : CrepProgHOL 64} {a b : Nat}
    (paid : LoopPaid context live t u p a) (le : a ≤ b) : LoopPaid context live t u p b := by
  obtain ⟨extra, wl, work, bound, rel⟩ := paid
  exact ⟨extra, wl, work, by omega, rel⟩

/-- Node-count Crep work transfers with the uniform factor 200. -/
theorem crep_loop_coarse_work {F : Type} (opt : LoopOptimiseWork) {t : CrepSemHOLState 64 F}
    {p : CrepProgHOL 64} {w : Nat} (work : CrepWork t p w)
    (u : LoopSemStateFiniteExact 64 F) (context : CrepToLoopContextExact) (live : NumSet)
    (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error) (rel : CrepLoopRel context live t u) :
    LoopPaid context live t u p (200 * w) := by
  obtain ⟨w', priced, bound⟩ := crepWork_coarse work
  exact (crep_loop_executed_work coarsePricing opt priced u context live ok rel).mono bound

/-- Exact-priced Crep work transfers with factor one. -/
theorem crep_loop_sharp_work {F : Type} (opt : LoopOptimiseWork) {t : CrepSemHOLState 64 F}
    {p : CrepProgHOL 64} {w : Nat} (work : CrepWorkS t p w)
    (u : LoopSemStateFiniteExact 64 F) (context : CrepToLoopContextExact) (live : NumSet)
    (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error) (rel : CrepLoopRel context live t u) :
    LoopPaid context live t u p w :=
  crep_loop_executed_work sharpPricing opt work u context live ok rel

#print axioms crepWork_coarse
#print axioms crep_loop_coarse_work
#print axioms crep_loop_sharp_work
end InitECandidate.Runtime.FineCost
