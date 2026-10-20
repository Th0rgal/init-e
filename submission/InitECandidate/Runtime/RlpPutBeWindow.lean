import InitECandidate.Runtime.RlpPutBeLoopWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The body equation of the actual `rlp_put_be`: `i := n; while 0 < i { … }; return 0`, so the byte
countdown starts at the requested length `n` and the trailing return touches no memory. -/
theorem source_rlpPutBe_body :
    sourceFunctionBody Guest.guestFn_rlp_put_be =
      .dec (ofString "i") .one (.var .local (ofString "n"))
        (.seq rlpPutBeLoop (.return (.const (0#64)))) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq,
    rlpPutBeLoop,rlpPutBeStep]
  rfl

#print axioms source_rlpPutBe_body

/-- A `return` statement writes no memory: it either errors out in place or installs its value over
cleared locals. -/
theorem return_memory {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (w : BitVec 64) :
    (evaluateHOLFiniteState s (.return e)).2.memory w = s.memory w := by
  rw [evaluateHOLFiniteState_return]
  split
  · rfl
  · split
    · simp [emptyLocalsHOLFinite]
    · rfl

#print axioms return_memory

/-- The actual `rlp_put_be` writes only inside `[dst, dst+n)`: its initializer installs the countdown
index `i := n`, the loop then stays inside that window, and the trailing `return 0` writes nothing. -/
theorem rlpPutBe_window {F : Type} (D N : BitVec 64) (w : BitVec 64) (out : ¬ MWin D N.toNat w)
    (s : PanSemStateFiniteExact 64 F)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N))) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_put_be)).2.memory w =
      s.memory w := by
  rw [source_rlpPutBe_body,evaluateHOLFiniteState_dec_total]
  dsimp only
  have initEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "n")) = some (.val (.word N)) := by
    simp [evalHOLExact,hn]
  rw [initEval]
  dsimp only
  have shapeTrue : shapeEqHOL .one (shapeOfHOLExact (.val (.word N))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeTrue]
  have hdst : (setVarHOLFinite (ofString "i") (.val (.word N)) s).locals.lookup (ofString "dst") =
      some (.val (.word D)) :=
    lookup_setVar_ne s (ofString "i") (ofString "dst") _ _ (by decide) hd
  have hi : (setVarHOLFinite (ofString "i") (.val (.word N)) s).locals.lookup (ofString "i") =
      some (.val (.word N)) :=
    lookup_setVar_eq s (ofString "i") _
  have hloop := rlpPutBeLoop_window D N w out
    (setVarHOLFinite (ofString "i") (.val (.word N)) s) N hdst hi (le_refl _)
  have bodyMemory : (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word N)) s)
      (.seq rlpPutBeLoop (.return (.const (0#64))))).2.memory w =
      (setVarHOLFinite (ofString "i") (.val (.word N)) s).memory w := by
    rw [evaluateHOLFiniteState_seq_line780]
    dsimp only
    split
    · rw [return_memory]
      exact hloop
    · exact hloop
  exact bodyMemory.trans rfl

#print axioms rlpPutBe_window

end InitECandidate.Runtime
