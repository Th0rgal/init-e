import InitECandidate.Runtime.GuestCostPcAdd
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

/-- The `sp` initialiser of the stack helpers: `ev[16]`. -/
noncomputable def stackPopSp : ExpHOL 64 := fundingLoad 16

/-- The empty-stack guard of `stack_pop`. -/
noncomputable def stackPopGuard : ExpHOL 64 :=
  .cmp Cmp.equal (.var VarKind.local (ofString "sp")) (.const 0)

/-- The rejection prefix of `stack_pop`: the empty-stack guard raises `EvmErr 2`
before the stack pointer is touched. -/
noncomputable def stackPopRejectPrefix : ProgHOL 64 :=
  .ite stackPopGuard (.raise (ofString "EvmErr") (.const 2)) .skip

/-- Recorded work of one empty-stack rejection of `stack_pop`. -/
noncomputable def stackPopRejectEvents (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64) :
    List WorkEvent :=
  let entry := setVarHOLFinite (ofString "sp") (.val (.word sp)) s
  .statement :: (expressionEvents s stackPopSp ++
    [.copy (flattenHOL (.val (.word sp))).length, .frame 1] ++
    (.statement :: (.statement :: (expressionEvents entry stackPopGuard ++
      (.statement :: (expressionEvents entry (.const 2) ++
        [.copy (flattenHOL (.val (.word (2 : BitVec 64)))).length]))))) ++
    [.copy (((s.locals.lookup (ofString "sp")).map
      (fun previous => (flattenHOL previous).length)).getD 0)])

/-- Post state of a rejected `stack_pop`: locals dropped, previous `sp` restored. -/
noncomputable def stackPopRejectPost (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  let post := emptyLocalsHOLFinite (setVarHOLFinite (ofString "sp") (.val (.word sp)) s)
  { post with locals := (HolFiniteMapExact.resVarEq post.locals
      (ofString "sp", s.locals.lookup (ofString "sp"))) }

/-- The stack pointer cell evaluates to the actual `sp` word. -/
theorem eval_stackPopSp (s : PanSemStateFiniteExact 64 F) (frame sp : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (domain : s.memaddrs (frame + 16)) (memory : s.memory (frame + 16) = .word sp) :
    expressionValue s stackPopSp = some (.val (.word sp)) :=
  eval_fundingLoad s frame 16 sp hFrame domain memory

/-- The empty-stack guard is true exactly when the pointer is zero. -/
theorem eval_stackPopGuard (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64)
    (hSp : s.locals.lookup (ofString "sp") = some (.val (.word sp))) :
    expressionValue s stackPopGuard =
      some (.val (.word (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.equal sp 0
        then 1 else 0))) := by
  classical
  unfold expressionValue stackPopGuard
  simp [evalHOLExact, toExact, hSp,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]


/-- The pinned rejection prefix is part of the installed `stack_pop` body. -/
theorem stackPop_prefix_installed :
    sourceFunctionBody Guest.guestFn_stack_pop =
      .dec (ofString "sp") .one stackPopSp
        (.seq stackPopRejectPrefix
          (.seq (.assign VarKind.local (ofString "sp")
              (.op .sub [.var VarKind.local (ofString "sp"), .const 1]))
            (.seq (.store (fundingAddress 16) (.var VarKind.local (ofString "sp")))
              (.return (.load (.comb [.one, .one, .one, .one])
                (.op .add [(.load .one (fundingAddress 8)),
                  (.panop .mul [.var VarKind.local (ofString "sp"), .const 32])])))))) := by
  cbv

/-- The empty-stack rejection of `stack_pop`, traced inside the installed body:
the guard raises `EvmErr 2` before either the stack pointer cell or the frame is
touched, so this is the additive terminal prefix of the pop loop. -/
theorem stackPop_reject_run (s : PanSemStateFiniteExact 64 F) (frame sp : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (domain : s.memaddrs (frame + 16)) (memory : s.memory (frame + 16) = .word sp)
    (exceptionShape : s.eshapes.lookup (ofString "EvmErr") = some .one)
    (empty : sp = 0) :
    StatementRun s (sourceFunctionBody Guest.guestFn_stack_pop)
      (some (.exception (ofString "EvmErr") (.val (.word 2))))
      (stackPopRejectPost s sp) (stackPopRejectEvents s sp) := by
  classical
  let entry := setVarHOLFinite (ofString "sp") (.val (.word sp)) s
  have entrySp : entry.locals.lookup (ofString "sp") = some (.val (.word sp)) := by
    simp [entry, setVarHOLFinite, FUPDATE]
  have init : CostedExpressionRun s stackPopSp (some (.val (.word sp)))
      (expressionEvents s stackPopSp) :=
    costedExpression_events s _ _ (eval_stackPopSp s frame sp hFrame domain memory)
  have guardValue : expressionValue entry stackPopGuard = some (.val (.word 1)) := by
    have := eval_stackPopGuard entry sp (by simpa [entry] using entrySp)
    rw [this]
    simp [empty, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have guard : CostedExpressionRun entry stackPopGuard (some (.val (.word 1)))
      (expressionEvents entry stackPopGuard) :=
    costedExpression_events entry stackPopGuard _ guardValue
  have payload : CostedExpressionRun entry (.const 2) (some (.val (.word 2)))
      (expressionEvents entry (.const 2)) :=
    costedExpression_events entry _ _ (by simp [expressionValue, evalHOLExact])
  have raiseRun : StatementRun entry (.raise (ofString "EvmErr") (.const 2))
      (some (.exception (ofString "EvmErr") (.val (.word 2)))) (emptyLocalsHOLFinite entry)
      (.statement :: (expressionEvents entry (.const 2) ++
        [.copy (flattenHOL (.val (.word (2 : BitVec 64)))).length])) :=
    StatementRun.raiseValue (exceptionId := ofString "EvmErr") (expression := .const 2)
      (shape := .one) payload exceptionShape (by simp [shapeOfHOLExact])
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have prefixRun : StatementRun entry stackPopRejectPrefix
      (some (.exception (ofString "EvmErr") (.val (.word 2)))) (emptyLocalsHOLFinite entry)
      (.statement :: (expressionEvents entry stackPopGuard ++
        (.statement :: (expressionEvents entry (.const 2) ++
          [.copy (flattenHOL (.val (.word (2 : BitVec 64)))).length])))) :=
    StatementRun.iteYes (post := emptyLocalsHOLFinite entry)
      (yes := .raise (ofString "EvmErr") (.const 2)) (no := .skip) guard (by decide) raiseRun
  have tailRun : StatementRun entry
      (.seq stackPopRejectPrefix
        (.seq (.assign VarKind.local (ofString "sp")
            (.op .sub [.var VarKind.local (ofString "sp"), .const 1]))
          (.seq (.store (fundingAddress 16) (.var VarKind.local (ofString "sp")))
            (.return (.load (.comb [.one, .one, .one, .one])
              (.op .add [(.load .one (fundingAddress 8)),
                (.panop .mul [.var VarKind.local (ofString "sp"), .const 32])]))))))
      (some (.exception (ofString "EvmErr") (.val (.word 2)))) (emptyLocalsHOLFinite entry)
      (.statement :: (.statement :: (expressionEvents entry stackPopGuard ++
        (.statement :: (expressionEvents entry (.const 2) ++
          [.copy (flattenHOL (.val (.word (2 : BitVec 64)))).length]))))) :=
    StatementRun.seqStop (by simp)

      (StatementRun.iteYes (post := emptyLocalsHOLFinite entry)
        (yes := .raise (ofString "EvmErr") (.const 2)) (no := .skip) guard (by decide) raiseRun)
  have shapeMatch : shapeEqHOL .one (shapeOfHOLExact (.val (.word sp))) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [stackPop_prefix_installed]
  refine StatementRun.declareValue (name := ofString "sp") (shape := .one)
    (initializer := stackPopSp)
    (body := (.seq stackPopRejectPrefix
      (.seq (.assign VarKind.local (ofString "sp")
          (.op .sub [.var VarKind.local (ofString "sp"), .const 1]))
        (.seq (.store (fundingAddress 16) (.var VarKind.local (ofString "sp")))
          (.return (.load (.comb [.one, .one, .one, .one])
            (.op .add [(.load .one (fundingAddress 8)),
              (.panop .mul [.var VarKind.local (ofString "sp"), .const 32])])))))))
    init shapeMatch ?_
  exact tailRun

#print axioms stackPop_prefix_installed
#print axioms stackPop_reject_run

#print axioms eval_stackPopSp
#print axioms eval_stackPopGuard
end InitECandidate.Runtime.FineCost
