import InitECandidate.Runtime.HashMemoryLayout
import InitECandidate.Runtime.PanDiscardCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem recordHash_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (function : MlS) (body : ProgHOL 64) (arguments : List (ExpHOL 64))
    (sha accelerator zeroHashes input heap out watched count : BitVec 64)
    (steps : List RecordHashStep) (fits : ∀ step ∈ steps, step.Fits count)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (small : count.toNat ≤ 134217712)
    (installed : state.code.lookup function = some ([(ofString "e",.one),(ofString "out",.one)],body,.one))
    (source : body = recordHashBody count steps)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word input),.val (.word out)])
    (budget : (1 + (2 + recordHashCost steps)) + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have lookup := pan_two_word_lookup state.code.lookup function (ofString "e") (ofString "out") body input out (by decide) installed
  obtain ⟨returned,output,bodyRun,_,scope⟩ := evaluate_discardCall_normal_result state post function .one arguments _ body _ args lookup run
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "e",.val (.word input))).update (ofString "out",.val (.word out)))
  have entryLayout : HashMemoryLayout entry sha accelerator zeroHashes heap out watched := layout.transfer rfl rfl
  have ctx : RecordHashEntryContext entry sha accelerator zeroHashes input heap out watched := entryLayout.recordEntry
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  rw [source] at bodyRun
  rw [scope]
  exact recordHash_body_returned_memory entry output sha accelerator zeroHashes input heap out watched count returned steps fits ctx small
    (by change 1 + (2 + recordHashCost steps) ≤ state.clock - 1; omega) bodyRun

#print axioms recordHash_call_normal_memory
end InitECandidate.Runtime
