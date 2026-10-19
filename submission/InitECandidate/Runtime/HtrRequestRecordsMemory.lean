import InitECandidate.Runtime.RecordHashCallMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrDeposit_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (sha accelerator zeroHashes input heap out watched : BitVec 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word input),.val (.word out)])
    (budget : htrDepositBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_deposit") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  exact recordHash_call_normal_memory state post (ofString "htr_deposit") (sourceFunctionBody Guest.guestFn_htr_deposit) arguments
    sha accelerator zeroHashes input heap out watched (5#64) depositHashSteps
    (by simp [depositHashSteps,RecordHashStep.Fits,RecordHashStep.Small,RecordHashStep.outputOffset]) layout (by decide)
    (by rw [layout.code]; exact originalRuntimeCode_htrDeposit_lookup)
    (by rw [sourceFunctionBody_eq_structural]; exact source_htrDeposit_record) args budget run

#print axioms htrDeposit_call_normal_memory

theorem htrWdreq_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (sha accelerator zeroHashes input heap out watched : BitVec 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word input),.val (.word out)])
    (budget : htrWdreqBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_wdreq") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  exact recordHash_call_normal_memory state post (ofString "htr_wdreq") (sourceFunctionBody Guest.guestFn_htr_wdreq) arguments
    sha accelerator zeroHashes input heap out watched (3#64) wdreqHashSteps
    (by simp [wdreqHashSteps,RecordHashStep.Fits,RecordHashStep.Small,RecordHashStep.outputOffset]) layout (by decide)
    (by rw [layout.code]; exact originalRuntimeCode_htrWdreq_lookup)
    (by rw [sourceFunctionBody_eq_structural]; exact source_htrWdreq_record) args budget run

#print axioms htrWdreq_call_normal_memory

theorem htrCons_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (sha accelerator zeroHashes input heap out watched : BitVec 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word input),.val (.word out)])
    (budget : htrConsBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_cons") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  exact recordHash_call_normal_memory state post (ofString "htr_cons") (sourceFunctionBody Guest.guestFn_htr_cons) arguments
    sha accelerator zeroHashes input heap out watched (3#64) consHashSteps
    (by simp [consHashSteps,RecordHashStep.Fits,RecordHashStep.Small,RecordHashStep.outputOffset]) layout (by decide)
    (by rw [layout.code]; exact originalRuntimeCode_htrCons_lookup)
    (by rw [sourceFunctionBody_eq_structural]; exact source_htrCons_record) args budget run

#print axioms htrCons_call_normal_memory

theorem htrBdep_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (sha accelerator zeroHashes input heap out watched : BitVec 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word input),.val (.word out)])
    (budget : htrBdepBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bdep") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  exact recordHash_call_normal_memory state post (ofString "htr_bdep") (sourceFunctionBody Guest.guestFn_htr_bdep) arguments
    sha accelerator zeroHashes input heap out watched (4#64) bdepHashSteps
    (by simp [bdepHashSteps,RecordHashStep.Fits,RecordHashStep.Small,RecordHashStep.outputOffset]) layout (by decide)
    (by rw [layout.code]; exact originalRuntimeCode_htrBdep_lookup)
    (by rw [sourceFunctionBody_eq_structural]; exact source_htrBdep_record) args budget run

#print axioms htrBdep_call_normal_memory

theorem htrBexit_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (sha accelerator zeroHashes input heap out watched : BitVec 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word input),.val (.word out)])
    (budget : htrBexitBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bexit") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  exact recordHash_call_normal_memory state post (ofString "htr_bexit") (sourceFunctionBody Guest.guestFn_htr_bexit) arguments
    sha accelerator zeroHashes input heap out watched (2#64) bexitHashSteps
    (by simp [bexitHashSteps,RecordHashStep.Fits,RecordHashStep.Small,RecordHashStep.outputOffset]) layout (by decide)
    (by rw [layout.code]; exact originalRuntimeCode_htrBexit_lookup)
    (by rw [sourceFunctionBody_eq_structural]; exact source_htrBexit_record) args budget run

#print axioms htrBexit_call_normal_memory

end InitECandidate.Runtime
