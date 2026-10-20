import InitECandidate.Runtime.GuestCostComb4Load
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


/-- The decrement expression of the successful path. -/
theorem eval_stackPopSub (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64)
    (hSp : s.locals.lookup (ofString "sp") = some (.val (.word sp))) :
    expressionValue s (.op .sub [.var VarKind.local (ofString "sp"), .const 1]) =
      some (.val (.word (sp - 1))) := by
  classical
  unfold expressionValue
  simp [evalHOLExact, evalListHOLExact, toExact, hSp, wordOpHOL, wordOp, valueIsWord, valueWord]

/-- The `sp := sp - 1` assignment of the successful path. -/
theorem stackPop_assign_run (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64)
    (hSp : s.locals.lookup (ofString "sp") = some (.val (.word sp))) :
    StatementRun s (.assign VarKind.local (ofString "sp")
      (.op .sub [.var VarKind.local (ofString "sp"), .const 1])) none
      (setKvarHOLFinite VarKind.local (ofString "sp")
        (.val (.word (sp - 1))) s)
      (.statement :: (expressionEvents s
        (.op .sub [.var VarKind.local (ofString "sp"), .const 1]) ++
        [.copy (flattenHOL (.val (.word (sp - 1)))).length])) := by
  classical
  refine StatementRun.assignValue (kind := VarKind.local) (name := ofString "sp")
    (expression := .op .sub [.var VarKind.local (ofString "sp"), .const 1])
    (value := .val (.word (sp - 1))) ?_ ?_
  · exact costedExpression_events s _ _ (eval_stackPopSub s sp hSp)
  · simp [isValidValueHOLFinite, lookupKvarHOLFinite, hSp, shapeOfHOLExact, shapeEqHOL]

/-- The stack-pointer store of the successful path. -/
theorem stackPop_store_run (s : PanSemStateFiniteExact 64 F) (frame sp' : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hSp : s.locals.lookup (ofString "sp") = some (.val (.word sp')))
    (domain : s.memaddrs (frame + 16)) :
    StatementRun s (.store (fundingAddress 16) (.var VarKind.local (ofString "sp"))) none
      { s with memory := writeWordMemory s (frame + 16) sp' }
      (.statement :: (expressionEvents s (fundingAddress 16) ++
        expressionEvents s (.var VarKind.local (ofString "sp")) ++
        [.memory (flattenHOL (.val (.word sp'))).length])) := by
  classical
  have dst : CostedExpressionRun s (fundingAddress 16) (some (.val (.word (frame + 16))))
      (expressionEvents s (fundingAddress 16)) :=
    costedExpression_events s _ _ (eval_fundingAddress s frame 16 hFrame)
  have src : CostedExpressionRun s (.var VarKind.local (ofString "sp")) (some (.val (.word sp')))
      (expressionEvents s (.var VarKind.local (ofString "sp"))) :=
    costedExpression_events s _ _ (by simp [expressionValue, evalHOLExact, hSp])
  have write : @panMemStoresHOL 64 _ (frame + 16) (flattenHOL (.val (.word sp'))) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory =
      some (writeWordMemory s (frame + 16) sp') := by
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL]
    rw [if_pos domain]
    rfl
  exact StatementRun.storeValue (destination := fundingAddress 16)
    (source := .var VarKind.local (ofString "sp")) dst src write



/-- Address expression of the popped word: `ev[8] + sp * 32`. -/
noncomputable def stackPopValueAddress : ExpHOL 64 :=
  .op .add [(.load .one (fundingAddress 8)),
    (.panop .mul [.var VarKind.local (ofString "sp"), .const 32])]

theorem panOpHOL_mul_pair (x y : BitVec 64) :
    Flapjack.panOpHOL .mul [x, y] = some (x * y) := rfl

/-- The popped word address evaluates from the actual frame word and pointer. -/
theorem eval_stackPopValueAddress (s : PanSemStateFiniteExact 64 F) (frame base sp' : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hBase : s.memaddrs (frame + 8)) (baseMemory : s.memory (frame + 8) = .word base)
    (hSp : s.locals.lookup (ofString "sp") = some (.val (.word sp'))) :
    @evalHOLExact 64 F _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) stackPopValueAddress =
      some (.val (.word (base + sp' * 32))) := by
  classical
  unfold stackPopValueAddress
  simp only [evalHOLExact, evalListHOLExact]
  have addrEval : @evalHOLExact 64 F _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) (fundingAddress 8) =
      some (.val (.word (frame + 8))) := eval_fundingAddress s frame 8 hFrame
  rw [addrEval]
  simp only [evalHOLExact, evalListHOLExact, memLoadHOLExact, hBase, baseMemory, if_true,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp [evalHOLExact, evalListHOLExact, toExact, hSp, valueIsWord, valueWord, wordOpHOL, wordOp,
    panOpHOL]

#print axioms panOpHOL_mul_pair
#print axioms eval_stackPopValueAddress
#print axioms eval_stackPopSub
#print axioms stackPop_assign_run
#print axioms stackPop_store_run


/-- The popped word: a four-word structured load at the computed address. -/
theorem stackPop_return_run (s : PanSemStateFiniteExact 64 F) (base w0 w1 w2 w3 : BitVec 64)
    (hAddress : expressionValue s stackPopValueAddress = some (.val (.word base)))
    (d0 : s.memaddrs base) (d1 : s.memaddrs (base + 8)) (d2 : s.memaddrs (base + 16))
    (d3 : s.memaddrs (base + 24))
    (m0 : s.memory base = .word w0) (m1 : s.memory (base + 8) = .word w1)
    (m2 : s.memory (base + 16) = .word w2) (m3 : s.memory (base + 24) = .word w3) :
    StatementRun s (.return (.load comb4Shape stackPopValueAddress))
      (some (.returned (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2),
        .val (.word w3)])))
      (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.load comb4Shape stackPopValueAddress) ++
        [.copy (flattenHOL (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2),
          .val (.word w3)])).length])) :=
  StatementRun.returnValue (expression := .load comb4Shape stackPopValueAddress)
    (costedExpression_events s _ _
      (eval_load_comb4 s stackPopValueAddress base w0 w1 w2 w3 hAddress d0 d1 d2 d3 m0 m1 m2 m3))
    (by simp [shapeOfHOLExact, comb4Shape])

#print axioms stackPop_return_run


/-- The empty-stack guard is false when the pointer is a nonzero word. -/
theorem eval_stackPopGuardNonzero (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64)
    (hSp : s.locals.lookup (ofString "sp") = some (.val (.word sp)))
    (nonzero : sp ≠ (0 : BitVec 64)) :
    expressionValue s stackPopGuard = some (.val (.word 0)) := by
  rw [eval_stackPopGuard s sp hSp]
  have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.equal sp 0 = false := by
    show (sp == (0 : BitVec 64)) = false
    by_cases h : sp = 0
    · exact absurd h nonzero
    · simpa using h
  rw [hcmp]
  rfl

/-- Recorded work of one successful `stack_pop`: initialiser, false guard, skip,
decrement, store, and the four-word return. -/
noncomputable def stackPopSuccessEvents (s : PanSemStateFiniteExact 64 F) (frame sp base : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64) : List WorkEvent :=
  let entry := setVarHOLFinite (ofString "sp") (.val (.word sp)) s
  let assigned := setKvarHOLFinite VarKind.local (ofString "sp") (.val (.word (sp - 1))) entry
  let stored := { assigned with memory := writeWordMemory assigned (frame + 16) (sp - 1) }
  let payload : ValueHOL 64 :=
    .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
  expressionEvents s stackPopSp ++
    [.copy (flattenHOL (.val (.word sp))).length, .frame 1] ++
    (.statement :: (.statement :: (expressionEvents entry stackPopGuard ++ [.statement]))) ++
    (.statement :: (.statement :: (expressionEvents entry
      (.op .sub [.var VarKind.local (ofString "sp"), .const 1]) ++
      [.copy (flattenHOL (.val (.word (sp - 1)))).length]))) ++
    (.statement :: (.statement :: (expressionEvents assigned (fundingAddress 16) ++
      expressionEvents assigned (.var VarKind.local (ofString "sp")) ++
      [.memory (flattenHOL (.val (.word (sp - 1)))).length]))) ++
    (.statement :: (.statement :: (expressionEvents stored (.load comb4Shape stackPopValueAddress) ++
      [.copy (flattenHOL payload).length]))) ++
    [.copy (((s.locals.lookup (ofString "sp")).map
      (fun previous => (flattenHOL previous).length)).getD 0)]

#print axioms eval_stackPopGuardNonzero

end InitECandidate.Runtime.FineCost
