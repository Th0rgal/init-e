import InitECandidate.Runtime.GuestCostStackPop
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace InitECandidate.Runtime.FineCost

variable {fn : MlS}

theorem stackPush_score_cost (coeff : Work) (n : Nat) :
    coeff.score (WorkEvent.cost n).units = coeff.nativeCost * n := by
  simp [Work.score, WorkEvent.units]
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

set_option maxHeartbeats 4000000

/-- A raw word-level memory write, the shape `panMemStoreHOL` produces. -/
def writeWordMem (memory : RiscV.Word 64 → HolWordLab 64) (address value : BitVec 64) :
    RiscV.Word 64 → HolWordLab 64 :=
  fun current => if current = address then .word value else memory current

/-- The memory after writing four consecutive words, the exact post-memory of a
successful structured store. -/
noncomputable def writeWord4Memory (s : PanSemStateFiniteExact 64 F) (base : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64) : RiscV.Word 64 → HolWordLab 64 :=
  writeWordMem (writeWordMem (writeWordMem (writeWordMem s.memory base w0)
    (base + panBytesInWord 64) w1) (base + panBytesInWord 64 + panBytesInWord 64) w2)
    (base + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64) w3

/-- A four-word structured store writes the four consecutive word cells. -/
theorem panMemStoresHOL_four (s : PanSemStateFiniteExact 64 F) (base : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64)
    (d0 : s.memaddrs base) (d1 : s.memaddrs (base + 8))
    (d2 : s.memaddrs (base + 8 + 8)) (d3 : s.memaddrs (base + 8 + 8 + 8)) :
    @panMemStoresHOL 64 _ base [.word w0, .word w1, .word w2, .word w3] s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory =
      some (writeWord4Memory s base w0 w1 w2 w3) := by
  classical
  have step0 : @panMemStoreHOL 64 _ base (.word w0) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory =
      some (writeWordMem s.memory base w0) := by
    rw [panMemStoreHOL]
    rw [if_pos d0]
    rfl
  have step1 : @panMemStoreHOL 64 _ (base + 8) (.word w1) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) (writeWordMem s.memory base w0) =
      some (writeWordMem (writeWordMem s.memory base w0) (base + 8) w1) := by
    rw [panMemStoreHOL]
    rw [if_pos d1]
    rfl
  have step2 : @panMemStoreHOL 64 _ (base + 8 + 8) (.word w2) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a))
      (writeWordMem (writeWordMem s.memory base w0) (base + 8) w1) =
      some (writeWordMem (writeWordMem (writeWordMem s.memory base w0) (base + 8) w1)
        (base + 8 + 8) w2) := by
    rw [panMemStoreHOL]
    rw [if_pos d2]
    rfl
  have step3 : @panMemStoreHOL 64 _ (base + 8 + 8 + 8) (.word w3) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a))
      (writeWordMem (writeWordMem (writeWordMem s.memory base w0) (base + 8) w1)
        (base + 8 + 8) w2) =
      some (writeWordMem (writeWordMem (writeWordMem (writeWordMem s.memory base w0)
        (base + 8) w1) (base + 8 + 8) w2) (base + 8 + 8 + 8) w3) := by
    rw [panMemStoreHOL]
    rw [if_pos d3]
    rfl
  rw [panMemStoresHOL_cons_some base (.word w0)
    [.word w1, .word w2, .word w3] s.memaddrs s.memory
    (writeWordMem s.memory base w0) step0]
  rw [panMemStoresHOL_cons_some (base + panBytesInWord 64) (.word w1)
    [.word w2, .word w3] s.memaddrs (writeWordMem s.memory base w0)
    (writeWordMem (writeWordMem s.memory base w0) (base + panBytesInWord 64) w1) step1]
  rw [panMemStoresHOL_cons_some (base + panBytesInWord 64 + panBytesInWord 64) (.word w2)
    [.word w3] s.memaddrs
    (writeWordMem (writeWordMem s.memory base w0) (base + panBytesInWord 64) w1)
    (writeWordMem (writeWordMem (writeWordMem s.memory base w0) (base + panBytesInWord 64) w1)
      (base + panBytesInWord 64 + panBytesInWord 64) w2) step2]
  rw [panMemStoresHOL_cons_some (base + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64)
    (.word w3) [] s.memaddrs
    (writeWordMem (writeWordMem (writeWordMem s.memory base w0) (base + panBytesInWord 64) w1)
      (base + panBytesInWord 64 + panBytesInWord 64) w2)
    (writeWordMem (writeWordMem (writeWordMem (writeWordMem s.memory base w0)
      (base + panBytesInWord 64) w1) (base + panBytesInWord 64 + panBytesInWord 64) w2)
      (base + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64) w3) step3]
  simp only [panMemStoresHOL_nil]
  rfl

/-- The pushed value is a four-word structure. -/
def stackPushValue (v0 v1 v2 v3 : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word v0), .val (.word v1), .val (.word v2), .val (.word v3)]

/-- The capacity guard of `stack_push`: false exactly while `sp < cap`. -/
theorem eval_stackPushCapacityGuard (s : PanSemStateFiniteExact 64 F) (sp cap : BitVec 64)
    (hSp : s.locals.lookup (ofString "sp") = some (.val (.word sp)))
    (hCap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (below : sp.toNat < cap.toNat) :
    expressionValue s
      (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
        (.var VarKind.local (ofString "cap"))) = some (.val (.word 0)) := by
  classical
  have lower : decide (sp < cap) = true := by
    simpa [BitVec.lt_def] using below
  unfold expressionValue
  simp [evalHOLExact, evalListHOLExact, toExact, hSp, hCap,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, lower]

/-- The full-stack guard of `stack_push`: false at any pointer other than 1024. -/
theorem eval_stackPushFullGuard (s : PanSemStateFiniteExact 64 F) (sp : BitVec 64)
    (hSp : s.locals.lookup (ofString "sp") = some (.val (.word sp)))
    (notFull : sp ≠ (1024 : BitVec 64)) :
    expressionValue s
      (.cmp Cmp.equal (.var VarKind.local (ofString "sp"))
        (.const (1024 : BitVec 64))) = some (.val (.word 0)) := by
  classical
  have hcmp : (sp == (1024 : BitVec 64)) = false := beq_eq_false_iff_ne.mpr notFull
  unfold expressionValue
  simp only [evalHOLExact, toExact, hSp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    hcmp, Bool.false_eq_true, if_false]

/-- The pinned installed body of `stack_push`. -/
noncomputable def stackPushGrowth : ProgHOL 64 :=
  .seq
    (.ite (.cmp Cmp.notLower (.var VarKind.local (ofString "cap"))
        (.const (1024 : BitVec 64)))
      (.raise (ofString "EvmErr") (.const (3 : BitVec 64))) .skip)
    (.dec (ofString "ncap") .one
      (.panop .mul [.var VarKind.local (ofString "cap"), .const (2 : BitVec 64)])
      (.seq
        (.ite (.cmp Cmp.lower (.const (1024 : BitVec 64))
            (.var VarKind.local (ofString "ncap")))
          (.assign VarKind.local (ofString "ncap") (.const (1024 : BitVec 64))) .skip)
        (.decCall (ofString "ns") .one (ofString "scratch_alloc")
          [(.panop .mul [.var VarKind.local (ofString "ncap"), .const (32 : BitVec 64)])]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [(.var VarKind.local (ofString "ns")),
                (.load .one (fundingAddress 8)),
                (.panop .mul [.var VarKind.local (ofString "sp"), .const (32 : BitVec 64)])])
            (.seq
              (.store (fundingAddress 8) (.var VarKind.local (ofString "ns")))
              (.store (fundingAddress 232) (.var VarKind.local (ofString "ncap"))))))))

noncomputable def stackPushTail : ProgHOL 64 :=
  .seq
    (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "sp"))
        (.const (1024 : BitVec 64)))
      (.raise (ofString "EvmErr") (.const (3 : BitVec 64))) .skip)
    (.seq
      (.store stackPopValueAddress (.var VarKind.local (ofString "v")))
      (.seq
        (.store (fundingAddress 16)
          (.op .add [.var VarKind.local (ofString "sp"), .const (1 : BitVec 64)]))
        (.return (.const (0 : BitVec 64)))))

noncomputable def stackPushBody : ProgHOL 64 :=
  .dec (ofString "sp") .one (fundingLoad 16)
    (.dec (ofString "cap") .one (fundingLoad 232)
      (.seq
        (.ite (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
            (.var VarKind.local (ofString "cap")))
          stackPushGrowth .skip)
        stackPushTail))

theorem source_stackPush_body :
    sourceFunctionBody Guest.guestFn_stack_push = stackPushBody := by
  cbv

/-- The state after the `sp` initialiser of `stack_push`. -/
noncomputable def stackPushCapEntry (s : PanSemStateFiniteExact 64 F) (sp cap : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "cap") (.val (.word cap)) (stackPopEntry s sp)

/-- The post-state of the successful adequate-capacity push. -/
noncomputable def stackPushPost (s : PanSemStateFiniteExact 64 F)
    (frame sp cap base v0 v1 v2 v3 : BitVec 64) : PanSemStateFiniteExact 64 F :=
  let entrySp := stackPopEntry s sp
  let entryCap := stackPushCapEntry s sp cap
  let address := base + sp * 32
  let stored := { entryCap with
    memory := writeWord4Memory entryCap address v0 v1 v2 v3 }
  let updated := { stored with memory := writeWordMemory stored (frame + 16) (sp + 1) }
  let cleared := emptyLocalsHOLFinite updated
  let capPost := { cleared with locals := (HolFiniteMapExact.resVarEq cleared.locals
    (ofString "cap", entrySp.locals.lookup (ofString "cap"))) }
  { capPost with locals := (HolFiniteMapExact.resVarEq capPost.locals
    (ofString "sp", s.locals.lookup (ofString "sp"))) }

/-- The exact recorded work of the adequate-capacity successful push. -/
noncomputable def stackPushSuccessEvents (s : PanSemStateFiniteExact 64 F)
    (frame sp cap base v0 v1 v2 v3 : BitVec 64) : List WorkEvent :=
  let entrySp := stackPopEntry s sp
  let entryCap := stackPushCapEntry s sp cap
  let address := base + sp * 32
  let payload := stackPushValue v0 v1 v2 v3
  let stored := { entryCap with
    memory := writeWord4Memory entryCap address v0 v1 v2 v3 }
  let updated := { stored with memory := writeWordMemory stored (frame + 16) (sp + 1) }
  let capGuard := expressionEvents entryCap
    (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
      (.var VarKind.local (ofString "cap")))
  let fullGuard := expressionEvents entryCap
    (.cmp Cmp.equal (.var VarKind.local (ofString "sp"))
      (.const (1024 : BitVec 64)))
  let storeV := .statement :: (expressionEvents entryCap stackPopValueAddress ++
    expressionEvents entryCap (.var VarKind.local (ofString "v")) ++
    [.memory (flattenHOL payload).length, .cost (storeOverhead (flattenHOL payload).length)])
  let storeSp := .statement :: (expressionEvents stored (fundingAddress 16) ++
    expressionEvents stored
      (.op .add [.var VarKind.local (ofString "sp"), .const (1 : BitVec 64)]) ++
    [.memory (flattenHOL (.val (.word (sp + 1)))).length, .cost (storeOverhead (flattenHOL (.val (.word (sp + 1)))).length)])
  let ret := .statement :: (expressionEvents updated (.const (0 : BitVec 64)) ++
    [.cost (returnOverhead (flattenHOL (.val (.word (0 : BitVec 64)))).length + returnMoves fn)])
  let tail := storeV ++ (storeSp ++ ret)
  let tailEvents := (.statement :: .cost (statementUnit + branchMoves fn) :: (fullGuard ++ [.statement])) ++ tail
  let bodyEvents := (.statement :: .cost (statementUnit + branchMoves fn) :: (capGuard ++ [.statement])) ++ tailEvents
  let capEvents := .statement :: (expressionEvents entrySp (fundingLoad 232) ++
    [.frame 1] ++ bodyEvents)
  .statement :: (expressionEvents s (fundingLoad 16) ++
    [.frame 1] ++ capEvents)

/-- The adequate-capacity successful path of the installed `stack_push`: `sp` and
`cap` are loaded, both guards take their `skip` branch, the four-word value is
stored at `ev[8] + sp * 32`, the pointer is incremented, and zero returned. -/
theorem stackPush_success_run (s : PanSemStateFiniteExact 64 F)
    (frame sp cap base v0 v1 v2 v3 : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spDomain : s.memaddrs (frame + 16))
    (spMemory : s.memory (frame + 16) = .word sp)
    (capDomain : s.memaddrs (frame + 232))
    (capMemory : s.memory (frame + 232) = .word cap)
    (hV : s.locals.lookup (ofString "v") =
      some (.rStruct [.val (.word v0), .val (.word v1), .val (.word v2), .val (.word v3)]))
    (baseDomain : s.memaddrs (frame + 8))
    (baseMemory : s.memory (frame + 8) = .word base)
    (below : sp.toNat < cap.toNat)
    (notFull : sp ≠ (1024 : BitVec 64))
    (storeDomain0 : s.memaddrs (base + sp * 32))
    (storeDomain1 : s.memaddrs (base + sp * 32 + 8))
    (storeDomain2 : s.memaddrs (base + sp * 32 + 8 + 8))
    (storeDomain3 : s.memaddrs (base + sp * 32 + 8 + 8 + 8)) :
    StatementRun fn s (sourceFunctionBody Guest.guestFn_stack_push)
      (some (.returned (.val (.word 0))))
      (stackPushPost s frame sp cap base v0 v1 v2 v3)
      (stackPushSuccessEvents (fn := fn) s frame sp cap base v0 v1 v2 v3) := by
  classical
  let entrySp := stackPopEntry s sp
  let entryCap := stackPushCapEntry s sp cap
  let address := base + sp * 32
  let payload := stackPushValue v0 v1 v2 v3
  let stored := { entryCap with memory := writeWord4Memory entryCap address v0 v1 v2 v3 }
  let updated := { stored with memory := writeWordMemory stored (frame + 16) (sp + 1) }
  have hSpEntry : entrySp.locals.lookup (ofString "sp") = some (.val (.word sp)) :=
    stackPopEntry_sp s sp
  have hCapEntry : entryCap.locals.lookup (ofString "cap") = some (.val (.word cap)) := by
    simp [entryCap, stackPushCapEntry, setVarHOLFinite, FUPDATE]
  have hSpCapEntry : entryCap.locals.lookup (ofString "sp") = some (.val (.word sp)) := by
    have names : (ofString "sp" : MlStringHOL) ≠ ofString "cap" := by decide_cbv
    simpa [entryCap, stackPushCapEntry, setVarHOLFinite, FUPDATE, names, Ne.symm names]
      using hSpEntry
  have hVCapEntry : entryCap.locals.lookup (ofString "v") =
      some (.rStruct [.val (.word v0), .val (.word v1), .val (.word v2), .val (.word v3)]) := by
    have n1 : (ofString "v" : MlStringHOL) ≠ ofString "cap" := by decide_cbv
    have n2 : (ofString "v" : MlStringHOL) ≠ ofString "sp" := by decide_cbv
    have hSp : entrySp.locals.lookup (ofString "v") =
        some (.rStruct [.val (.word v0), .val (.word v1), .val (.word v2), .val (.word v3)]) := by
      have names : (ofString "v" : MlStringHOL) ≠ ofString "sp" := by decide_cbv
      simpa [entrySp, stackPopEntry, setVarHOLFinite, FUPDATE, names, Ne.symm names] using hV
    simpa [entryCap, stackPushCapEntry, setVarHOLFinite, FUPDATE, n1, Ne.symm n1] using hSp
  have hFrameEntry : entrySp.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    simpa [entrySp, stackPopEntry, setVarHOLFinite] using hFrame
  have hFrameCap : entryCap.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    simpa [entryCap, stackPushCapEntry, setVarHOLFinite] using hFrameEntry
  have hCapMemory : entrySp.memory (frame + 232) = .word cap := by
    simpa [entrySp, stackPopEntry, setVarHOLFinite] using capMemory
  have capDomainEntry : entrySp.memaddrs (frame + 232) := by
    simpa [entrySp, stackPopEntry, setVarHOLFinite] using capDomain
  have hBaseDomainCap : entryCap.memaddrs (frame + 8) := by
    simpa [entryCap, stackPushCapEntry, stackPopEntry, setVarHOLFinite] using baseDomain
  have hBaseMemoryCap : entryCap.memory (frame + 8) = .word base := by
    simpa [entryCap, stackPushCapEntry, entrySp, stackPopEntry, setVarHOLFinite] using baseMemory
  have spInit : CostedExpressionRun s (fundingLoad 16) (some (.val (.word sp)))
      (expressionEvents s (fundingLoad 16)) :=
    costedExpression_events s _ _ (eval_fundingLoad s frame 16 sp hFrame spDomain spMemory)
  have spShape : shapeEqHOL .one (shapeOfHOLExact (.val (.word sp))) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have capInit : CostedExpressionRun entrySp (fundingLoad 232) (some (.val (.word cap)))
      (expressionEvents entrySp (fundingLoad 232)) :=
    costedExpression_events entrySp _ _
      (eval_fundingLoad entrySp frame 232 cap hFrameEntry capDomainEntry hCapMemory)
  have capShape : shapeEqHOL .one (shapeOfHOLExact (.val (.word cap))) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have capGuardValue : expressionValue entryCap
      (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
        (.var VarKind.local (ofString "cap"))) = some (.val (.word 0)) :=
    eval_stackPushCapacityGuard entryCap sp cap hSpCapEntry hCapEntry below
  have capGuard : CostedExpressionRun entryCap
      (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
        (.var VarKind.local (ofString "cap")))
      (some (.val (.word 0)))
      (expressionEvents entryCap
        (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
          (.var VarKind.local (ofString "cap")))) :=
    costedExpression_events entryCap _ _ capGuardValue
  have growthRun : StatementRun fn entryCap (.ite
      (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
        (.var VarKind.local (ofString "cap")))
      stackPushGrowth .skip) none entryCap
      (.statement :: .cost (statementUnit + branchMoves fn) :: (expressionEvents entryCap
        (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
          (.var VarKind.local (ofString "cap"))) ++ [.statement])) :=
    StatementRun.iteNo (fn := fn) (r := none) (post := entryCap) (bodyEvents := [.statement])
      (yes := stackPushGrowth) (no := .skip) capGuard (StatementRun.skip (fn := fn) entryCap)
  have fullGuardValue : expressionValue entryCap
      (.cmp Cmp.equal (.var VarKind.local (ofString "sp"))
        (.const (1024 : BitVec 64))) = some (.val (.word 0)) :=
    eval_stackPushFullGuard entryCap sp hSpCapEntry notFull
  have fullGuard : CostedExpressionRun entryCap
      (.cmp Cmp.equal (.var VarKind.local (ofString "sp"))
        (.const (1024 : BitVec 64))) (some (.val (.word 0)))
      (expressionEvents entryCap
        (.cmp Cmp.equal (.var VarKind.local (ofString "sp"))
          (.const (1024 : BitVec 64)))) :=
    costedExpression_events entryCap _ _ fullGuardValue
  have fullRun : StatementRun fn entryCap (.ite
      (.cmp Cmp.equal (.var VarKind.local (ofString "sp"))
        (.const (1024 : BitVec 64)))
      (.raise (ofString "EvmErr") (.const (3 : BitVec 64))) .skip) none entryCap
      (.statement :: .cost (statementUnit + branchMoves fn) :: (expressionEvents entryCap
        (.cmp Cmp.equal (.var VarKind.local (ofString "sp"))
          (.const (1024 : BitVec 64))) ++ [.statement])) :=
    StatementRun.iteNo (fn := fn) (r := none) (post := entryCap) (bodyEvents := [.statement])
      (yes := .raise (ofString "EvmErr") (.const (3 : BitVec 64))) (no := .skip)
      fullGuard (StatementRun.skip (fn := fn) entryCap)
  have addressValue : expressionValue entryCap stackPopValueAddress =
      some (.val (.word address)) := by
    have := eval_stackPopValueAddress entryCap frame base sp
      hFrameCap hBaseDomainCap hBaseMemoryCap hSpCapEntry
    simpa [expressionValue, address] using this
  have addressExpr : CostedExpressionRun entryCap stackPopValueAddress
      (some (.val (.word address))) (expressionEvents entryCap stackPopValueAddress) :=
    costedExpression_events entryCap _ _ addressValue
  have valueExpr : CostedExpressionRun entryCap (.var VarKind.local (ofString "v"))
      (some payload) (expressionEvents entryCap (.var VarKind.local (ofString "v"))) :=
    costedExpression_events entryCap _ _ (by
      simpa [payload, stackPushValue, expressionValue, evalHOLExact, toExact] using hVCapEntry)
  have domains : entryCap.memaddrs address ∧
      entryCap.memaddrs (address + 8) ∧
      entryCap.memaddrs (address + 8 + 8) ∧
      entryCap.memaddrs (address + 8 + 8 + 8) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [entryCap, stackPushCapEntry, stackPopEntry, setVarHOLFinite, address] using storeDomain0
    · simpa [entryCap, stackPushCapEntry, stackPopEntry, setVarHOLFinite, address] using storeDomain1
    · simpa [entryCap, stackPushCapEntry, stackPopEntry, setVarHOLFinite, address] using storeDomain2
    · simpa [entryCap, stackPushCapEntry, stackPopEntry, setVarHOLFinite, address] using storeDomain3
  have writeV : @panMemStoresHOL 64 _ address (flattenHOL payload) entryCap.memaddrs
      (fun a => Classical.propDecidable (entryCap.memaddrs a)) entryCap.memory =
      some (writeWord4Memory entryCap address v0 v1 v2 v3) := by
    simpa [payload, stackPushValue, flattenHOL] using
      panMemStoresHOL_four entryCap address v0 v1 v2 v3
        domains.1 domains.2.1 domains.2.2.1 domains.2.2.2
  have storeVRun : StatementRun fn entryCap
      (.store stackPopValueAddress (.var VarKind.local (ofString "v"))) none stored
      (.statement :: (expressionEvents entryCap stackPopValueAddress ++
        expressionEvents entryCap (.var VarKind.local (ofString "v")) ++
        [.memory (flattenHOL payload).length, .cost (storeOverhead (flattenHOL payload).length)])) :=
    StatementRun.storeValue (fn := fn) (destination := stackPopValueAddress)
      (source := .var VarKind.local (ofString "v")) addressExpr valueExpr writeV
  have storedSp : stored.locals.lookup (ofString "sp") = some (.val (.word sp)) := by
    simpa [stored] using hSpCapEntry
  have storedFrame : stored.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    simpa [stored] using hFrameCap
  have addressStoredExpr : CostedExpressionRun stored (fundingAddress 16)
      (some (.val (.word (frame + 16)))) (expressionEvents stored (fundingAddress 16)) :=
    costedExpression_events stored _ _ (eval_fundingAddress stored frame 16 storedFrame)
  have spValueExpr : CostedExpressionRun stored
      (.op .add [.var VarKind.local (ofString "sp"), .const (1 : BitVec 64)])
      (some (.val (.word (sp + 1))))
      (expressionEvents stored
        (.op .add [.var VarKind.local (ofString "sp"), .const (1 : BitVec 64)])) :=
    costedExpression_events stored _ _ (by
      simp [expressionValue, evalHOLExact, evalListHOLExact, toExact, storedSp,
        wordOpHOL, wordOp, valueIsWord, valueWord])
  have entryCapSpDomain : entryCap.memaddrs (frame + 16) := by
    simpa [entryCap, stackPushCapEntry, stackPopEntry, setVarHOLFinite] using spDomain
  have storedDomain : stored.memaddrs (frame + 16) := by
    simpa [stored] using entryCapSpDomain
  have writeSp : @panMemStoresHOL 64 _ (frame + 16)
      (flattenHOL (.val (.word (sp + 1)))) stored.memaddrs
      (fun a => Classical.propDecidable (stored.memaddrs a)) stored.memory =
      some (writeWordMemory stored (frame + 16) (sp + 1)) := by
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL]
    rw [if_pos storedDomain]
    rfl
  have storeSpRun : StatementRun fn stored
      (.store (fundingAddress 16)
        (.op .add [.var VarKind.local (ofString "sp"), .const (1 : BitVec 64)])) none updated
      (.statement :: (expressionEvents stored (fundingAddress 16) ++
        expressionEvents stored
          (.op .add [.var VarKind.local (ofString "sp"), .const (1 : BitVec 64)]) ++
        [.memory (flattenHOL (.val (.word (sp + 1)))).length, .cost (storeOverhead (flattenHOL (.val (.word (sp + 1)))).length)])) :=
    StatementRun.storeValue (fn := fn) (destination := fundingAddress 16)
      (source := .op .add [.var VarKind.local (ofString "sp"), .const (1 : BitVec 64)])
      addressStoredExpr spValueExpr writeSp
  have retRun : StatementRun fn updated (.return (.const (0 : BitVec 64)))
      (some (.returned (.val (.word 0)))) (emptyLocalsHOLFinite updated)
      (.statement :: (expressionEvents updated (.const (0 : BitVec 64)) ++
        [.cost (returnOverhead (flattenHOL (.val (.word (0 : BitVec 64)))).length + returnMoves fn)])) :=
    StatementRun.returnValue (fn := fn) (expression := .const (0 : BitVec 64))
      (costedExpression_events updated _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have tailRun := StatementRun.seqNext (fn := fn) fullRun
    (StatementRun.seqNext (fn := fn) storeVRun (StatementRun.seqNext (fn := fn) storeSpRun retRun))
  have bodyRun := StatementRun.seqNext (fn := fn) growthRun tailRun
  have capRun := StatementRun.declareValue (fn := fn) (name := ofString "cap") (shape := .one)
    (initializer := fundingLoad 232)
    (body := (.seq (.ite (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
        (.var VarKind.local (ofString "cap"))) stackPushGrowth .skip) stackPushTail))
    capInit capShape (by simpa [entryCap, entrySp, stackPushCapEntry, stackPopEntry, stackPushTail] using bodyRun)
  rw [source_stackPush_body]
  refine StatementRun.declareValue (fn := fn) (name := ofString "sp") (shape := .one)
    (initializer := fundingLoad 16)
    (body := (.dec (ofString "cap") .one (fundingLoad 232)
      (.seq (.ite (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
          (.var VarKind.local (ofString "cap"))) stackPushGrowth .skip)
        stackPushTail)))
    spInit spShape ?_
  simpa [stackPushSuccessEvents, stackPushBody, stackPushPost, stackPushGrowth,
    stackPushTail, stackPushCapEntry, stackPopEntry, stackPushValue, stored, updated,
    address, payload, entrySp, entryCap] using capRun

/-- Explicit coefficient price of the same successful adequate-capacity push. -/
theorem stackPushSuccessEvents_score (coeff : Work) {fn : MlS} (s : PanSemStateFiniteExact 64 F)
    (frame sp cap base v0 v1 v2 v3 : BitVec 64) :
    coeff.score (executionWork
      (stackPushSuccessEvents (fn := fn) s frame sp cap base v0 v1 v2 v3)) ≤
      let entrySp := stackPopEntry s sp
      let entryCap := stackPushCapEntry s sp cap
      let address := base + sp * 32
      let payload := stackPushValue v0 v1 v2 v3
      let stored := { entryCap with
        memory := writeWord4Memory entryCap address v0 v1 v2 v3 }
      let updated := { stored with memory := writeWordMemory stored (frame + 16) (sp + 1) }
      13 * coeff.statements +
        expressionCost coeff s (fundingLoad 16) +
        coeff.movedWords * (flattenHOL (.val (.word sp))).length +
        coeff.frameSlots * 1 +
        expressionCost coeff entrySp (fundingLoad 232) +
        coeff.movedWords * (flattenHOL (.val (.word cap))).length +
        coeff.frameSlots * 1 +
        expressionCost coeff entryCap
          (.cmp Cmp.notLower (.var VarKind.local (ofString "sp"))
            (.var VarKind.local (ofString "cap"))) +
        expressionCost coeff entryCap
          (.cmp Cmp.equal (.var VarKind.local (ofString "sp"))
            (.const (1024 : BitVec 64))) +
        expressionCost coeff entryCap stackPopValueAddress +
        expressionCost coeff entryCap (.var VarKind.local (ofString "v")) +
        coeff.memoryAccesses * (flattenHOL payload).length +
        coeff.nativeCost * storeOverhead (flattenHOL payload).length +
        expressionCost coeff stored (fundingAddress 16) +
        expressionCost coeff stored
          (.op .add [.var VarKind.local (ofString "sp"), .const (1 : BitVec 64)]) +
        coeff.memoryAccesses * (flattenHOL (.val (.word (sp + 1)))).length +
        coeff.nativeCost * storeOverhead (flattenHOL (.val (.word (sp + 1)))).length +
        expressionCost coeff updated (.const (0 : BitVec 64)) +
        coeff.movedWords * (flattenHOL (.val (.word (0 : BitVec 64)))).length +
        coeff.movedWords * (((entrySp.locals.lookup (ofString "cap")).map
          (fun previous => (flattenHOL previous).length)).getD 0) +
        coeff.movedWords * (((s.locals.lookup (ofString "sp")).map
          (fun previous => (flattenHOL previous).length)).getD 0) +
        2 * coeff.score (WorkEvent.cost (statementUnit + branchMoves fn)).units +
        coeff.score (WorkEvent.cost (returnOverhead (flattenHOL (.val (.word (0 : BitVec 64)))).length + returnMoves fn)).units := by
  unfold stackPushSuccessEvents expressionCost
  dsimp only [stackPopEntry, stackPushCapEntry, stackPushValue]
  simp only [executionWork_score_cons, executionWork_score_append, score_statement,
    guest_score_copy, score_frame, guest_score_memory, score_singleton, score_expression,
    executionWork_nil_score, List.append_nil, stackPush_score_cost]
  omega

#print axioms panMemStoresHOL_four
#print axioms eval_stackPushCapacityGuard
#print axioms eval_stackPushFullGuard
#print axioms source_stackPush_body
#print axioms stackPush_success_run
#print axioms stackPushSuccessEvents_score

end InitECandidate.Runtime.FineCost
