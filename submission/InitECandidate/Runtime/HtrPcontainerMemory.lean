import InitECandidate.Runtime.HtrPcontainerAllocationMemory
import InitECandidate.Runtime.HtrPcontainerBodyBound
import InitECandidate.Runtime.HeapMarkCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrPcontainer_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes heap chunks out count watched : BitVec 64) (value : ValueHOL 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 256) (budget : htrPcontainerBodyCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_pcontainer) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have enough : 1 ≤ state.clock := by unfold htrPcontainerBodyCost at budget; omega
  obtain ⟨marked,_,clock,memory,globals,locals,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap layout.code layout.atHeap (by omega)
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrPcontainerAt 0) = _ at run
  rw [source_htrPcontainer_mark,declaration] at run
  let next := setVarHOLFinite (ofString "mark") (.val (.word heap)) marked
  change (let output := evaluateHOLFiniteState next (htrPcontainerAt 1);
    (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "mark",state.locals.lookup (ofString "mark"))})) =
      (some (.returned value),post) at run
  cases tailRun : evaluateHOLFiniteState next (htrPcontainerAt 1) with
  | mk result inner =>
    rw [tailRun] at run
    obtain ⟨resultEq,postEq⟩ := Prod.mk.inj run
    change result = some (.returned value) at resultEq
    subst result
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    have nextLayout : HashMemoryLayout next sha accelerator zeroHashes heap out watched :=
      layout.transfer globals installed
    have remaining : htrPcontainerAllocationCost ≤ next.clock := by
      change _ ≤ marked.clock
      unfold htrPcontainerBodyCost at budget
      omega
    have frame := htrPcontainer_allocation_returned_memory next inner sha accelerator zeroHashes heap chunks out heap count watched value
      nextLayout ((keep _ (by decide)).trans atChunks) ((keep _ (by decide)).trans atOut)
      (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      ((keep _ (by decide)).trans atCount) small remaining tailRun
    rw [← postEq]
    exact frame.trans (congrFun memory watched)

/-- The actual original progressive-container call preserves every word
outside the output/SHA workspaces and before its fresh allocations. This
covers the payload's 19 fields and the requests container's 5 fields. -/
theorem htrPcontainer_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (sha accelerator zeroHashes heap chunks count out watched : BitVec 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word chunks),.val (.word count),.val (.word out)])
    (small : count.toNat ≤ 256) (budget : htrPcontainerBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_pcontainer") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "htr_pcontainer") =
      some ([(ofString "ch",.one),(ofString "n",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_pcontainer,.one) := by
    rw [layout.code]; exact originalRuntimeCode_htrPcontainer_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htr_pcontainer") (ofString "ch") (ofString "n")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_pcontainer) chunks count out
    (by decide) (by decide) (by decide) installed
  obtain ⟨value,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_pcontainer")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_pcontainer) _ args lookup run
  let entry := callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "ch",.val (.word chunks))).update
      (ofString "n",.val (.word count))).update (ofString "out",.val (.word out)))
  rw [postEq]
  exact htrPcontainer_body_returned_memory entry output sha accelerator zeroHashes heap chunks out count watched value
    (layout.transfer rfl rfl)
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    small (by change htrPcontainerBodyCost ≤ state.clock - 1; omega) bodyRun

#print axioms htrPcontainer_body_returned_memory
#print axioms htrPcontainer_call_normal_memory
end InitECandidate.Runtime
