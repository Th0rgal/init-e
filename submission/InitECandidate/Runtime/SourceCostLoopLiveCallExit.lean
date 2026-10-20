import InitECandidate.Runtime.SourceCostLoopLiveCallHandle
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- A callee exit which reaches neither continuation nor handler keeps its
exact callee work; unexecuted handler programs incur no charge. -/
theorem loop_live_paid_call_ret_handler {F : Type}
    {s entry post : LoopSemStateFiniteExact 64 F} {names arguments : List Nat}
    {live liveOut : NumSet} {target : Option Nat} {exceptionName : Nat}
    {handlerProgram continuation : HolLoopProg 64} {values : List (WordLocW 64)} {result : Option (LoopResultExact 64)}
    {env : Spt (WordLocW 64)} {prog : HolLoopProg 64} {wb : Nat}
    (args : getVars arguments s = some values)
    (find : findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : cutRes live (none, s) = (none, entry))
    (body : LoopWork { entry with locals := env } prog (result, post) wb)
    (plain : loopRetPlain result names (some (exceptionName, handlerProgram, continuation, liveOut)))
    (nonerror : (loopRetExit result post entry names).1 ≠ some .error) :
    LoopLivePaid s (.call (some (names, live)) target arguments
      (some (exceptionName, handlerProgram, continuation, liveOut)))
      (loopRetExit result post entry names) (1 + arguments.length + wb + loopRetWords result) := by
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
  have targetArgs := live_argument_values s locals arguments saved input args
  have savedInput : sptSubspt (sptInter s.locals saved) locals :=
    live_projection_weaken input (fun key member => (sptMem_sptUnion _ _ key).mpr (Or.inr member))
  obtain ⟨entryLocals, targetCut, footprint⟩ := live_projection_cut s locals live saved needed savedInput
    (fun key member => ((live_mem_inter live needed key).mp member).1)
    (fun key member inside => (live_mem_inter live needed key).mpr ⟨inside, member⟩)
    (by rw [cut]; simp)
  rw [cut] at targetCut footprint
  have targetBody : LoopWork { { entry with locals := entryLocals } with locals := env }
      prog (result, post) wb := body
  have targetPlain : loopRetPlain result names
      (some (exceptionName, handlerCode, contCode, sptInter wanted liveOut)) := by
    cases result with
    | none => exact plain
    | some r => cases r <;> exact plain
  have targetRun := LoopWork.callRet targetArgs find nodup targetCut targetBody targetPlain
  have target' : LoopWork { s with locals := locals }
      (shrinkHOL contexts (.call (some (names, live)) target arguments
        (some (exceptionName, handlerProgram, continuation, liveOut))) wanted).1
      (loopRetExit result post { entry with locals := entryLocals } names)
      (1 + arguments.length + wb + loopRetWords result) := by
    simpa only [compiled] using targetRun
  exact loop_live_finish (LoopWork.callRet args find nodup cut body plain) nonerror
    contexts locals wanted (by simpa only [compiled] using input) target' (by omega)

#print axioms loop_live_paid_call_ret_handler
end InitECandidate.Runtime.FineCost
