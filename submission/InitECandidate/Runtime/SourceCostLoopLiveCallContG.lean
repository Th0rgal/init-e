import InitECandidate.Runtime.SourceCostLoopLiveCallFrameG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice} {f : Nat}

/-- A returning call charges the unchanged callee once, extends saved-local
ownership by the returned values, and charges only its reached continuation. -/
theorem loop_live_paid_call_contG {F : Type}
    {s entry post : LoopSemStateFiniteExact 64 F} {names arguments : List Nat}
    {live liveOut : NumSet} {target : Option Nat} {exceptionName : Nat}
    {handlerProgram continuation : HolLoopProg 64} {values returned : List (WordLocW 64)}
    {env : Spt (WordLocW 64)} {prog : HolLoopProg 64} {output} {wb wc : Nat}
    (args : getVars arguments s = some values)
    (find : findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : cutRes live (none, s) = (none, entry))
    (body : LoopWorkG L (loopCallee target values) { entry with locals := env } prog (some (.result returned), post) wb)
    (lengths : returned.length = names.length)
    (cont : LoopWorkG L f (setVars names returned { post with locals := entry.locals }) continuation output wc)
    (paid : LoopLivePaidG L f (setVars names returned { post with locals := entry.locals }) continuation output wc)
    (nonerror : (cutRes liveOut output).1 ≠ some .error) :
    LoopLivePaidG L f s (.call (some (names, live)) target arguments
      (some (exceptionName, handlerProgram, continuation, liveOut)))
      (cutRes liveOut output) (196 + 39 * arguments.length + L.cs f (loopCallee target values) + L.rn names.length + wb +
        49 * returned.length + wc) := by
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
  have oldInput : sptSubspt (sptInter entry.locals (sptListDelete names contLive)) entryLocals :=
    live_projection_weakenG footprint (fun key member => (sptMem_sptUnion _ _ key).mpr (Or.inl member))
  have returnInput := live_projection_returnG entry.locals entryLocals names returned contLive lengths.symm oldInput
  have contInput : sptSubspt
      (sptInter (setVars names returned { post with locals := entry.locals }).locals
        (shrinkHOL contexts continuation wanted).2)
      (sptAlistInsert names returned entryLocals) := by
    simpa only [setVars, contCompiled] using returnInput
  obtain ⟨postLocals, wc', targetCont, bound, related⟩ :=
    paid contexts (sptAlistInsert names returned entryLocals) wanted contInput
  rw [contCompiled] at targetCont
  have targetCont' : LoopWorkG L f
      (setVars names returned { post with locals := entryLocals }) contCode
      (output.1, { output.2 with locals := postLocals }) wc' := by
    simpa only [setVars] using targetCont
  have targetBody : LoopWorkG L (loopCallee target values) { { entry with locals := entryLocals } with locals := env }
      prog (some (.result returned), post) wb := body
  have targetRun := LoopWorkG.callRetCont (f := f) (exceptionName := exceptionName) (handlerProgram := handlerCode)
    (liveOut := sptInter wanted liveOut) targetArgs find nodup targetCut targetBody lengths targetCont'
  have target' : LoopWorkG L f { s with locals := locals }
      (shrinkHOL contexts (.call (some (names, live)) target arguments
        (some (exceptionName, handlerProgram, continuation, liveOut))) wanted).1
      (cutRes (sptInter wanted liveOut) (output.1, { output.2 with locals := postLocals }))
      (196 + 39 * arguments.length + L.cs f (loopCallee target values) + L.rn names.length + wb +
        49 * returned.length + wc') := by
    simpa only [compiled] using targetRun
  exact loop_live_finishG (LoopWorkG.callRetCont (exceptionName := exceptionName) (handlerProgram := handlerProgram)
    (liveOut := liveOut) args find nodup cut body lengths cont) nonerror
    contexts locals wanted (by simpa only [compiled] using input) target' (by omega)

#print axioms loop_live_paid_call_contG
end InitECandidate.Runtime.FineCost
