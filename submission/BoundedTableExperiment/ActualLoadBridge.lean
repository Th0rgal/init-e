import CandidateFindLeafShape
import ActualLinkMemoryInvariant
import InitECandidate.Runtime.LoadOneRead
import InitECandidate.Runtime.RlpPutBeMemoryWindow

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 1000000

/-- Evaluate a `local + offset` address ending in the expected word. -/
theorem eval_localAddr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (base offset : BitVec 64)
    (hlocal : s.locals.lookup name = some (.val (.word base))) :
    expressionValue s (localAddr name offset) =
      some (.val (.word (base + offset))) := by
  simp [localAddr, expressionValue, evalHOLExact, evalListHOLExact, hlocal,
    wordOpHOL, wordOp, valueIsWord, valueWord]

/-- Evaluate a bare local word (the zero arm's address). -/
theorem eval_localWord {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (word : BitVec 64)
    (hlocal : s.locals.lookup name = some (.val (.word word))) :
    expressionValue s (.var .local name) = some (.val (.word word)) := by
  simpa [expressionValue, evalHOLExact] using hlocal

/-- Concrete `.dec` split of `candidateFindLeafRoute`. -/
theorem candidateFindLeafRoute_dec_split {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafRoute none post events) :
    ∃ (value : ValueHOL 64) (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s (.load .one (localAddr (ofString "node") 16))
        (some value) initEvents ∧
      post = { bodyPost with locals :=
        (HolFiniteMapExact.resVarEq bodyPost.locals
          (ofString "route", s.locals.lookup (ofString "route"))) } ∧
      StatementRun fn (setVarHOLFinite (ofString "route") value s)
        candidateFindLeafByte none bodyPost bodyEvents := by
  rw [candidateFindLeaf_route] at run
  cases run with
  | declareValue init shapeMatch bodyRun =>
      exact ⟨_, _, _, _, rfl, init, rfl, bodyRun⟩

/-- The route variable is the actual word at `node + 16`. -/
theorem candidateFindLeafRoute_route {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {node left right route : BitVec 64}
    (run : StatementRun fn s candidateFindLeafRoute none post events)
    (inv : NodeLinkInv s node left right route)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node))) :
    ∃ (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s (.load .one (localAddr (ofString "node") 16))
        (some (.val (.word route))) initEvents ∧
      post = { bodyPost with locals :=
        (HolFiniteMapExact.resVarEq bodyPost.locals
          (ofString "route", s.locals.lookup (ofString "route"))) } ∧
      StatementRun fn
        (setVarHOLFinite (ofString "route") (.val (.word route)) s)
        candidateFindLeafByte none bodyPost bodyEvents ∧
      s.memaddrs (node + 16) := by
  obtain ⟨value, initEvents, bodyEvents, bodyPost, eventsEq, init, postEq, bodyRun⟩ :=
    candidateFindLeafRoute_dec_split run
  have loaded := init.sound
  unfold expressionValue at loaded
  obtain ⟨pointer, word, addrEval, dom, cell, valueEq⟩ :=
    eval_load_one_read s (localAddr (ofString "node") 16) value loaded
  have addrWord := eval_localAddr s (ofString "node") node 16 nodeLocal
  have addrEval' :
      @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a))
        (localAddr (ofString "node") 16) =
        some (.val (.word (node + 16))) := by
    simpa [expressionValue] using addrWord
  have pointerEq : pointer = node + 16 :=
    HolWordLab.word.inj
      (ValueHOL.val.inj (Option.some.inj (addrEval.symm.trans addrEval')))
  have wordEq : word = route := by
    rw [pointerEq, inv.routeAt] at cell
    exact (HolWordLab.word.inj cell).symm
  have valueEq' : value = .val (.word route) := by
    simpa [wordEq] using valueEq
  refine ⟨initEvents, bodyEvents, bodyPost, eventsEq, ?_, postEq, ?_, ?_⟩
  · simpa [valueEq'] using init
  · simpa [valueEq'] using bodyRun
  · simpa [pointerEq] using dom

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateFindLeafRoute_dec_split
#print axioms BoundedTableExperiment.candidateFindLeafRoute_route

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Mask expression `route ^^^ 255`. -/
theorem eval_candidateFindLeafMask {F : Type} (s : PanSemStateFiniteExact 64 F)
    (route : BitVec 64)
    (routeLocal : s.locals.lookup (ofString "route") = some (.val (.word route))) :
    expressionValue s
      (.op .xor [.var .local (ofString "route"),.const (BitVec.ofNat 64 255)]) =
      some (.val (.word (route ^^^ BitVec.ofNat 64 255))) := by
  simp [expressionValue, evalHOLExact, evalListHOLExact, routeLocal,
    wordOpHOL, wordOp, valueIsWord, valueWord]

/-- Child-selection guard `(b &&& m) != 0`. -/
theorem eval_candidateFindLeafChildGuard {F : Type}
    (s : PanSemStateFiniteExact 64 F) (b m : BitVec 64)
    (bLocal : s.locals.lookup (ofString "b") = some (.val (.word b)))
    (mLocal : s.locals.lookup (ofString "m") = some (.val (.word m))) :
    expressionValue s
      (.cmp .notEqual (.op .and [.var .local (ofString "b"),.var .local (ofString "m")])
        (.const (0 : BitVec 64))) =
      some (.val (.word (if b &&& m = 0 then 0 else 1))) := by
  have hand : AndOp.and b (AndOp.and m (18446744073709551615#64)) = b &&& m := by
    change b &&& (m &&& 18446744073709551615#64) = b &&& m
    bv_decide
  simp [expressionValue, evalHOLExact, evalListHOLExact, bLocal, mLocal,
    wordOpHOL, wordOp, valueIsWord, valueWord, hand,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem candidateFindLeafChild_links {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {node left right route b m : BitVec 64}
    (run : StatementRun fn s candidateFindLeafChild none post events)
    (inv : NodeLinkInv s node left right route)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node)))
    (bLocal : s.locals.lookup (ofString "b") = some (.val (.word b)))
    (mLocal : s.locals.lookup (ofString "m") = some (.val (.word m))) :
    ∃ (flag : BitVec 64) (guardEvents branchEvents : List WorkEvent),
      events = .statement :: .cost (statementUnit + branchMoves fn) ::
        (guardEvents ++ branchEvents) ∧
      CostedExpressionRun s
        (.cmp .notEqual
          (.op .and [.var .local (ofString "b"),.var .local (ofString "m")])
          (.const (0 : BitVec 64)))
        (some (.val (.word flag))) guardEvents ∧
      flag = (if b &&& m = 0 then (0#64) else (1#64)) ∧
      post.locals.lookup (ofString "node") =
        some (.val (.word (if b &&& m = 0 then left else right))) ∧
      post.memory = s.memory ∧
      (b &&& m ≠ 0 → s.memaddrs (node + 8)) ∧
      (b &&& m = 0 → s.memaddrs node) := by
  rw [candidateFindLeaf_child] at run
  cases run with
  | iteYes guard nonzero body =>
      have gv := guard.sound
      rw [eval_candidateFindLeafChildGuard s b m bLocal mLocal] at gv
      have hb : b &&& m ≠ 0 := by
        intro hz
        rw [if_pos (by simpa using hz)] at gv
        injection gv with hv
        exact nonzero (by simpa using hv.symm)
      let flag : BitVec 64 := if b &&& m = 0 then (0#64) else (1#64)
      have guard' : CostedExpressionRun s
          (.cmp .notEqual (.op .and [.var .local (ofString "b"),.var .local (ofString "m")])
            (.const (0 : BitVec 64))) (some (.val (.word flag))) _ :=
        ⟨by rw [eval_candidateFindLeafChildGuard s b m bLocal mLocal]; simp [flag], guard.events_eq⟩
      cases body with
      | assignValue expr valid =>
          have loaded := expr.sound
          unfold expressionValue at loaded
          obtain ⟨pointer, word, addrEval, dom, cell, valueEq⟩ :=
            eval_load_one_read s (localAddr (ofString "node") 8) _ loaded
          have addrWord := eval_localAddr s (ofString "node") node 8 nodeLocal
          have addrEval' :
              @evalHOLExact 64 F _ s.toExact
                (fun a => Classical.propDecidable (s.memaddrs a))
                (localAddr (ofString "node") 8) = some (.val (.word (node + 8))) := by
            simpa [expressionValue] using addrWord
          have pointerEq : pointer = node + 8 :=
            HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (addrEval.symm.trans addrEval')))
          have wordEq : word = right := by
            rw [pointerEq, inv.rightAt] at cell
            exact (HolWordLab.word.inj cell).symm
          refine ⟨flag, _, _, rfl, guard', by simp [flag], ?_, rfl, ?_, ?_⟩
          · rw [if_neg hb]
            simpa [setKvarHOLFinite, valueEq, wordEq] using lookup_setVar_eq s (ofString "node") (ValueHOL.val (HolWordLab.word right))
          · intro _; simpa [pointerEq] using dom
          · intro hz; exact absurd hz hb
  | iteNo guard body =>
      have gv := guard.sound
      rw [eval_candidateFindLeafChildGuard s b m bLocal mLocal] at gv
      have hz : b &&& m = 0 := by
        by_contra hne
        rw [if_neg hne] at gv
        injection gv with hv
        injection hv with hw
        exact (by decide : (1#64) ≠ 0) (HolWordLab.word.inj hw)
      let flag : BitVec 64 := (0#64)
      have guard' : CostedExpressionRun s
          (.cmp .notEqual (.op .and [.var .local (ofString "b"),.var .local (ofString "m")])
            (.const (0 : BitVec 64))) (some (.val (.word flag))) _ :=
        ⟨by rw [eval_candidateFindLeafChildGuard s b m bLocal mLocal]; simp [flag, hz], guard.events_eq⟩
      cases body with
      | assignValue expr valid =>
          have loaded := expr.sound
          unfold expressionValue at loaded
          obtain ⟨pointer, word, addrEval, dom, cell, valueEq⟩ :=
            eval_load_one_read s (.var .local (ofString "node")) _ loaded
          have addrWord := eval_localWord s (ofString "node") node nodeLocal
          have addrEval' :
              @evalHOLExact 64 F _ s.toExact
                (fun a => Classical.propDecidable (s.memaddrs a))
                (.var .local (ofString "node")) = some (.val (.word node)) := by
            simpa [expressionValue] using addrWord
          have pointerEq : pointer = node :=
            HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (addrEval.symm.trans addrEval')))
          have wordEq : word = left := by
            rw [pointerEq, inv.leftAt] at cell
            exact (HolWordLab.word.inj cell).symm
          refine ⟨flag, _, _, rfl, guard', by simp [flag, hz], ?_, rfl, ?_, ?_⟩
          · have hz' : b &&& m = 0#64 := by simpa using hz
            simp only [hz', if_true]
            simpa [setKvarHOLFinite, valueEq, wordEq] using lookup_setVar_eq s (ofString "node") (ValueHOL.val (HolWordLab.word left))
          · intro hb; exact absurd hz hb
          · intro _; simpa [pointerEq] using dom
end BoundedTableExperiment

#print axioms BoundedTableExperiment.eval_candidateFindLeafMask
#print axioms BoundedTableExperiment.eval_candidateFindLeafChildGuard
#print axioms BoundedTableExperiment.candidateFindLeafChild_links
