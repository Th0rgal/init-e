import InitECandidate.Runtime.SourceCostLoopLiveCallContG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice} {f : Nat}

/-- An exception call charges the unchanged callee once, extends the saved
footprint by its exception binding, and charges only the actual handler. -/
theorem loop_live_paid_call_handleG {F : Type}
    {s entry post : LoopSemStateFiniteExact 64 F} {names arguments : List Nat}
    {live liveOut : NumSet} {target : Option Nat} {exceptionName : Nat}
    {handlerProgram continuation : HolLoopProg 64} {values : List (WordLocW 64)} {exn : WordLocW 64}
    {env : Spt (WordLocW 64)} {prog : HolLoopProg 64} {output} {wb wh : Nat}
    (args : getVars arguments s = some values)
    (find : findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : cutRes live (none, s) = (none, entry))
    (body : LoopWorkG L (loopCallee target values) { entry with locals := env } prog (some (.exception exn), post) wb)
    (cont : LoopWorkG L f (setVar exceptionName exn { post with locals := entry.locals }) handlerProgram output wh)
    (paid : LoopLivePaidG L f (setVar exceptionName exn { post with locals := entry.locals }) handlerProgram output wh)
    (nonerror : (cutRes liveOut output).1 ≠ some .error) :
    LoopLivePaidG L f s (.call (some (names, live)) target arguments
      (some (exceptionName, handlerProgram, continuation, liveOut)))
      (cutRes liveOut output) (L.call + L.cont + L.argCost arguments.length + L.cs f (loopCallee target values) + L.rn names.length + wb + wh) := by
  intro contexts locals wanted input
  rcases contCompiled : shrinkHOL contexts continuation wanted with ⟨contCode, contLive⟩
  rcases handlerCompiled : shrinkHOL contexts handlerProgram wanted with ⟨handlerCode, handlerLive⟩
  let needed := sptUnion (sptListDelete names contLive) (sptDelete exceptionName handlerLive)
  let saved := sptInter live needed
  have compiled : shrinkHOL contexts
      (.call (some (names, live)) target arguments
        (some (exceptionName, handlerProgram, continuation, liveOut))) wanted =
      (.call (some (names, saved)) target arguments
        (some (exceptionName, handlerCode, contCode, sptInter wanted liveOut)),
        sptUnion (sptFromAList (arguments.map fun x => (x, ()))) saved) := by
    simp only [shrinkHOL, contCompiled, handlerCompiled, saved, needed]
  rw [compiled] at input
  have targetArgs := live_argument_valuesG s locals arguments saved input args
  have savedInput : sptSubspt (sptInter s.locals saved) locals :=
    live_projection_weakenG input (fun key member => (sptMem_sptUnion _ _ key).mpr (Or.inr member))
  obtain ⟨entryLocals, targetCut, footprint⟩ := live_projection_cutG s locals live saved needed savedInput
    (fun key member => ((live_mem_interG live needed key).mp member).1)
    (fun key member inside => (live_mem_interG live needed key).mpr ⟨inside, member⟩)
    (by rw [cut]; simp)
  rw [cut] at targetCut footprint
  have oldInput : sptSubspt (sptInter entry.locals (sptDelete exceptionName handlerLive)) entryLocals :=
    live_projection_weakenG footprint (fun key member => (sptMem_sptUnion _ _ key).mpr (Or.inr member))
  have returnInput := live_projection_exceptionG entry.locals entryLocals exceptionName exn handlerLive oldInput
  have contInput : sptSubspt
      (sptInter (setVar exceptionName exn { post with locals := entry.locals }).locals
        (shrinkHOL contexts handlerProgram wanted).2)
      (sptInsert exceptionName exn entryLocals) := by
    simpa only [setVar, handlerCompiled] using returnInput
  obtain ⟨postLocals, wh', targetCont, bound, related⟩ :=
    paid contexts (sptInsert exceptionName exn entryLocals) wanted contInput
  rw [handlerCompiled] at targetCont
  have targetCont' : LoopWorkG L f
      (setVar exceptionName exn { post with locals := entryLocals }) handlerCode
      (output.1, { output.2 with locals := postLocals }) wh' := by
    simpa only [setVar] using targetCont
  have targetBody : LoopWorkG L (loopCallee target values) { { entry with locals := entryLocals } with locals := env }
      prog (some (.exception exn), post) wb := body
  have targetRun := LoopWorkG.callHandle (f := f) (continuation := contCode)
    (liveOut := sptInter wanted liveOut) targetArgs find nodup targetCut targetBody targetCont'
  have target' : LoopWorkG L f { s with locals := locals }
      (shrinkHOL contexts (.call (some (names, live)) target arguments
        (some (exceptionName, handlerProgram, continuation, liveOut))) wanted).1
      (cutRes (sptInter wanted liveOut) (output.1, { output.2 with locals := postLocals }))
      (L.call + L.cont + L.argCost arguments.length + L.cs f (loopCallee target values) + L.rn names.length + wb + wh') := by
    simpa only [compiled] using targetRun
  exact loop_live_finishG (LoopWorkG.callHandle (continuation := continuation)
    (liveOut := liveOut) args find nodup cut body cont) nonerror
    contexts locals wanted (by simpa only [compiled] using input) target' (by omega)

#print axioms loop_live_paid_call_handleG
end InitECandidate.Runtime.FineCost
