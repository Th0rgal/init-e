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
    [.frame 1] ++
    (.statement :: .cost statementUnit :: (expressionEvents entry stackPopGuard ++
      (.statement :: (expressionEvents entry (.const 2) ++
        [.cost (raiseOverhead (flattenHOL (.val (.word (2 : BitVec 64)))).length)])))))

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
        [.cost (raiseOverhead (flattenHOL (.val (.word (2 : BitVec 64)))).length)])) :=
    StatementRun.raiseValue (exceptionId := ofString "EvmErr") (expression := .const 2)
      (shape := .one) payload exceptionShape (by simp [shapeOfHOLExact])
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have prefixRun : StatementRun entry stackPopRejectPrefix
      (some (.exception (ofString "EvmErr") (.val (.word 2)))) (emptyLocalsHOLFinite entry)
      (.statement :: .cost statementUnit :: (expressionEvents entry stackPopGuard ++
        (.statement :: (expressionEvents entry (.const 2) ++
          [.cost (raiseOverhead (flattenHOL (.val (.word (2 : BitVec 64)))).length)])))) :=
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
      (.statement :: .cost statementUnit :: (expressionEvents entry stackPopGuard ++
        (.statement :: (expressionEvents entry (.const 2) ++
          [.cost (raiseOverhead (flattenHOL (.val (.word (2 : BitVec 64)))).length)])))) :=
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
        [.memory (flattenHOL (.val (.word sp'))).length, .cost (storeOverhead (flattenHOL (.val (.word sp'))).length)])) := by
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
        [.cost (returnOverhead (flattenHOL (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2),
          .val (.word w3)])).length)])) :=
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

/-- The state after the `sp` initialiser of `stack_pop` has run. -/
noncomputable def stackPopEntry (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "sp") (.val (.word sp)) s

/-- The state after the successful `sp := sp - 1` assignment. -/
noncomputable def stackPopAssigned (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  setKvarHOLFinite VarKind.local (ofString "sp") (.val (.word (sp - 1))) (stackPopEntry s sp)

/-- The actual post-store state of the successful path: the decremented pointer
is written into the `ev[16]` cell, leaving every other cell untouched. -/
noncomputable def stackPopStored (s : PanSemStateFiniteExact 64 F) (frame sp : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  { stackPopAssigned s sp with
    memory := writeWordMemory (stackPopAssigned s sp) (frame + 16) (sp - 1) }

/-- The initialiser leaves the pointer in the `sp` local. -/
theorem stackPopEntry_sp (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64) :
    (stackPopEntry s sp).locals.lookup (ofString "sp") = some (.val (.word sp)) := by
  simp [stackPopEntry, setVarHOLFinite, FUPDATE]

/-- The assignment leaves the decremented pointer in the `sp` local. -/
theorem stackPopAssigned_sp (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64) :
    (stackPopAssigned s sp).locals.lookup (ofString "sp") =
      some (.val (.word (sp - 1))) := by
  simp [stackPopAssigned, stackPopEntry, setKvarHOLFinite, setVarHOLFinite, FUPDATE]

/-- The store does not change the locals, so the post-store pointer is `sp - 1`. -/
theorem stackPopStored_sp (s : PanSemStateFiniteExact 64 F) (frame sp : BitVec 64) :
    (stackPopStored s frame sp).locals.lookup (ofString "sp") =
      some (.val (.word (sp - 1))) := by
  simpa [stackPopStored] using stackPopAssigned_sp s sp

/-- The popped-word address `ev[8]` and the written pointer cell `ev[16]` never
coincide in a 64-bit frame. -/
theorem stackPop_frameCell_distinct (frame : BitVec 64) :
    (frame + 8 : BitVec 64) ≠ frame + 16 := by
  intro h
  have h2 : (frame.toNat + 8) % 2 ^ 64 = (frame.toNat + 16) % 2 ^ 64 := by
    simpa [BitVec.toNat_add] using congrArg BitVec.toNat h
  omega

/-- The store of the decremented pointer leaves the `ev[8]` base cell intact. -/
theorem stackPopStored_baseCell (s : PanSemStateFiniteExact 64 F) (frame sp base : BitVec 64)
    (hBase : (stackPopAssigned s sp).memory (frame + 8) = .word base) :
    (stackPopStored s frame sp).memory (frame + 8) = .word base := by
  simp only [stackPopStored, writeWordMemory,
    if_neg (stackPop_frameCell_distinct frame)]
  exact hBase

/-- Recorded work of one successful `stack_pop`: the real statement trace of
initialiser, false guard, skip, decrement, store, and the four-word return. -/
noncomputable def stackPopSuccessEvents (s : PanSemStateFiniteExact 64 F) (frame sp _base : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64) : List WorkEvent :=
  let entry := stackPopEntry s sp
  let assigned := stackPopAssigned s sp
  let stored := stackPopStored s frame sp
  let payload : ValueHOL 64 :=
    .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
  .statement ::
    (expressionEvents s stackPopSp ++
      [.frame 1] ++
      ((.statement :: .cost statementUnit :: (expressionEvents entry stackPopGuard ++ [.statement])) ++
        (.statement :: (expressionEvents entry
            (.op .sub [.var VarKind.local (ofString "sp"), .const 1]) ++
          [.copy (flattenHOL (.val (.word (sp - 1)))).length])) ++
        .statement :: (expressionEvents assigned (fundingAddress 16) ++
          expressionEvents assigned (.var VarKind.local (ofString "sp")) ++
          [.memory (flattenHOL (.val (.word (sp - 1)))).length, .cost (storeOverhead (flattenHOL (.val (.word (sp - 1)))).length)]) ++
        .statement :: (expressionEvents stored
          (.load comb4Shape stackPopValueAddress) ++
          [.cost (returnOverhead (flattenHOL payload).length)])))

/-- The complete successful execution trace of the installed `stack_pop` helper:
the nonzero pointer takes the guard's false branch, the pointer is decremented and
stored, and the four popped words are returned. The popped-word cells are the
actual cells of the real post-store state. -/
theorem stackPop_success_run (state : PanSemStateFiniteExact 64 F)
    (frame sp base w0 w1 w2 w3 : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (domain : state.memaddrs (frame + 16))
    (memory : state.memory (frame + 16) = .word sp)
    (nonzero : sp ≠ (0 : BitVec 64))
    (baseDomain : state.memaddrs (frame + 8))
    (baseCell : state.memory (frame + 8) = .word base)
    (addressDomain0 : (stackPopStored state frame sp).memaddrs (base + (sp - 1) * 32))
    (addressDomain1 : (stackPopStored state frame sp).memaddrs (base + (sp - 1) * 32 + 8))
    (addressDomain2 : (stackPopStored state frame sp).memaddrs (base + (sp - 1) * 32 + 16))
    (addressDomain3 : (stackPopStored state frame sp).memaddrs (base + (sp - 1) * 32 + 24))
    (addressCell0 : (stackPopStored state frame sp).memory (base + (sp - 1) * 32) = .word w0)
    (addressCell1 : (stackPopStored state frame sp).memory (base + (sp - 1) * 32 + 8) = .word w1)
    (addressCell2 : (stackPopStored state frame sp).memory (base + (sp - 1) * 32 + 16) = .word w2)
    (addressCell3 : (stackPopStored state frame sp).memory (base + (sp - 1) * 32 + 24) = .word w3) :
    StatementRun state (sourceFunctionBody Guest.guestFn_stack_pop)
      (some (.returned (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2),
        .val (.word w3)])))
      { emptyLocalsHOLFinite (stackPopStored state frame sp) with
        locals := HolFiniteMapExact.resVarEq
          (emptyLocalsHOLFinite (stackPopStored state frame sp)).locals
          (ofString "sp", state.locals.lookup (ofString "sp")) }
      (stackPopSuccessEvents state frame sp (base + (sp - 1) * 32) w0 w1 w2 w3) := by
  classical
  have entrySp : (stackPopEntry state sp).locals.lookup (ofString "sp") =
      some (.val (.word sp)) := stackPopEntry_sp state sp
  have entryFrame : (stackPopEntry state sp).globals.lookup (ofString "ev") =
      some (.val (.word frame)) := by
    simpa [stackPopEntry, setVarHOLFinite] using hFrame
  have assignedFrame : (stackPopAssigned state sp).globals.lookup (ofString "ev") =
      some (.val (.word frame)) := by
    simpa [stackPopAssigned, stackPopEntry, setKvarHOLFinite, setVarHOLFinite] using entryFrame
  have assignedSp : (stackPopAssigned state sp).locals.lookup (ofString "sp") =
      some (.val (.word (sp - 1))) := stackPopAssigned_sp state sp
  have assignedDomain : (stackPopAssigned state sp).memaddrs (frame + 16) := by
    simpa [stackPopAssigned, stackPopEntry, setKvarHOLFinite, setVarHOLFinite] using domain
  have assignedBaseDomain : (stackPopAssigned state sp).memaddrs (frame + 8) := by
    simpa [stackPopAssigned, stackPopEntry, setKvarHOLFinite, setVarHOLFinite] using baseDomain
  have assignedBaseCell : (stackPopAssigned state sp).memory (frame + 8) = .word base := by
    simpa [stackPopAssigned, stackPopEntry, setKvarHOLFinite, setVarHOLFinite] using baseCell
  have storedFrame : (stackPopStored state frame sp).globals.lookup (ofString "ev") =
      some (.val (.word frame)) := by
    simpa [stackPopStored] using assignedFrame
  have storedBaseDomain : (stackPopStored state frame sp).memaddrs (frame + 8) := by
    simpa [stackPopStored] using assignedBaseDomain
  have storedBaseCell : (stackPopStored state frame sp).memory (frame + 8) = .word base :=
    stackPopStored_baseCell state frame sp base assignedBaseCell
  have storedSp : (stackPopStored state frame sp).locals.lookup (ofString "sp") =
      some (.val (.word (sp - 1))) := stackPopStored_sp state frame sp
  have init : CostedExpressionRun state stackPopSp (some (.val (.word sp)))
      (expressionEvents state stackPopSp) :=
    costedExpression_events state _ _ (eval_stackPopSp state frame sp hFrame domain memory)
  have shapeMatch : shapeEqHOL .one (shapeOfHOLExact (.val (.word sp))) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have guardValue : expressionValue (stackPopEntry state sp) stackPopGuard =
      some (.val (.word 0)) :=
    eval_stackPopGuardNonzero (stackPopEntry state sp) sp entrySp nonzero
  have guard : CostedExpressionRun (stackPopEntry state sp) stackPopGuard (some (.val (.word 0)))
      (expressionEvents (stackPopEntry state sp) stackPopGuard) :=
    costedExpression_events _ _ _ guardValue
  have iteRun : StatementRun (stackPopEntry state sp)
      (.ite stackPopGuard (.raise (ofString "EvmErr") (.const 2)) .skip)
      none (stackPopEntry state sp)
      (.statement :: .cost statementUnit :: (expressionEvents (stackPopEntry state sp) stackPopGuard ++
        [.statement])) :=
    StatementRun.iteNo (r := none) (post := stackPopEntry state sp)
      (bodyEvents := [.statement]) (yes := .raise (ofString "EvmErr") (.const 2))
      (no := .skip) guard (StatementRun.skip (stackPopEntry state sp))
  have assignRun : StatementRun (stackPopEntry state sp)
      (.assign VarKind.local (ofString "sp")
        (.op .sub [.var VarKind.local (ofString "sp"), .const 1]))
      none (stackPopAssigned state sp)
      (.statement :: (expressionEvents (stackPopEntry state sp)
          (.op .sub [.var VarKind.local (ofString "sp"), .const 1]) ++
        [.copy (flattenHOL (.val (.word (sp - 1)))).length])) :=
    stackPop_assign_run (stackPopEntry state sp) sp entrySp
  have storeRun : StatementRun (stackPopAssigned state sp)
      (.store (fundingAddress 16) (.var VarKind.local (ofString "sp")))
      none (stackPopStored state frame sp)
      (.statement :: (expressionEvents (stackPopAssigned state sp) (fundingAddress 16) ++
        expressionEvents (stackPopAssigned state sp) (.var VarKind.local (ofString "sp")) ++
        [.memory (flattenHOL (.val (.word (sp - 1)))).length, .cost (storeOverhead (flattenHOL (.val (.word (sp - 1)))).length)])) :=
    stackPop_store_run (stackPopAssigned state sp) frame (sp - 1) assignedFrame assignedSp
      assignedDomain
  have address : expressionValue (stackPopStored state frame sp) stackPopValueAddress =
      some (.val (.word (base + (sp - 1) * 32))) := by
    have := eval_stackPopValueAddress (stackPopStored state frame sp) frame base (sp - 1)
      storedFrame storedBaseDomain storedBaseCell storedSp
    simpa [expressionValue] using this
  have retRun : StatementRun (stackPopStored state frame sp)
      (.return (.load comb4Shape stackPopValueAddress))
      (some (.returned (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2),
        .val (.word w3)])))
      (emptyLocalsHOLFinite (stackPopStored state frame sp))
      (.statement :: (expressionEvents (stackPopStored state frame sp)
          (.load comb4Shape stackPopValueAddress) ++
        [.cost (returnOverhead (flattenHOL (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2),
          .val (.word w3)])).length)])) :=
    stackPop_return_run (stackPopStored state frame sp) (base + (sp - 1) * 32)
      w0 w1 w2 w3 address addressDomain0 addressDomain1 addressDomain2 addressDomain3
      addressCell0 addressCell1 addressCell2 addressCell3
  have tailRun := StatementRun.seqNext assignRun (StatementRun.seqNext storeRun retRun)
  rw [stackPop_prefix_installed]
  refine StatementRun.declareValue (name := ofString "sp") (shape := .one)
    (initializer := stackPopSp)
    (body := (.seq (.ite stackPopGuard (.raise (ofString "EvmErr") (.const 2)) .skip)
      (.seq (.assign VarKind.local (ofString "sp")
          (.op .sub [.var VarKind.local (ofString "sp"), .const 1]))
        (.seq (.store (fundingAddress 16) (.var VarKind.local (ofString "sp")))
          (.return (.load comb4Shape stackPopValueAddress))))))
    init shapeMatch ?_
  simpa [stackPopSuccessEvents, stackPopEntry, stackPopAssigned, stackPopStored] using
    StatementRun.seqNext iteRun tailRun

/-- Explicit coefficient price of the same successful `stack_pop` trace: nine
executed statements, four expressions, three copied values, one frame slot, one
word write, and the restored previous pointer. -/
theorem stackPopSuccessEvents_score (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (frame sp base : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    coeff.score (executionWork (stackPopSuccessEvents s frame sp base w0 w1 w2 w3)) ≤
      9 * coeff.statements +
        expressionCost coeff s stackPopSp +
        coeff.movedWords * (flattenHOL (.val (.word sp))).length +
        coeff.frameSlots * 1 +
        expressionCost coeff (stackPopEntry s sp) stackPopGuard +
        expressionCost coeff (stackPopEntry s sp)
          (.op .sub [.var VarKind.local (ofString "sp"), .const 1]) +
        coeff.movedWords * (flattenHOL (.val (.word (sp - 1)))).length +
        expressionCost coeff (stackPopAssigned s sp) (fundingAddress 16) +
        expressionCost coeff (stackPopAssigned s sp) (.var VarKind.local (ofString "sp")) +
        coeff.memoryAccesses * (flattenHOL (.val (.word (sp - 1)))).length +
        coeff.nativeCost * storeOverhead (flattenHOL (.val (.word (sp - 1)))).length +
        expressionCost coeff (stackPopStored s frame sp)
          (.load comb4Shape stackPopValueAddress) +
        coeff.movedWords * (flattenHOL (.rStruct [.val (.word w0), .val (.word w1),
          .val (.word w2), .val (.word w3)])).length +
        coeff.movedWords * (((s.locals.lookup (ofString "sp")).map
          (fun previous => (flattenHOL previous).length)).getD 0) +
        coeff.score (WorkEvent.cost statementUnit).units +
        coeff.score (WorkEvent.cost (returnOverhead (flattenHOL (.rStruct [.val (.word w0),
          .val (.word w1), .val (.word w2), .val (.word w3)])).length)).units := by
  unfold stackPopSuccessEvents expressionCost
  dsimp only [stackPopEntry, stackPopAssigned, stackPopStored]
  simp only [executionWork_score_cons, executionWork_score_append, score_statement,
    guest_score_copy, score_frame, guest_score_memory, score_singleton, score_expression,
    executionWork_nil_score, List.append_nil, charge_score_cost]
  omega

#print axioms stackPopEntry_sp
#print axioms stackPopAssigned_sp
#print axioms stackPopStored_sp
#print axioms stackPop_frameCell_distinct
#print axioms stackPop_success_run
#print axioms stackPopSuccessEvents_score

end InitECandidate.Runtime.FineCost
