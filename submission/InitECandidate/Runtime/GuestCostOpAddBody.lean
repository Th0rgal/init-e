import InitECandidate.Runtime.GuestCostOpAddCompose
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 4000000

/-- The post state of one successful `stack_pop` helper execution, exactly as
`stackPop_success_run` reports it. -/
noncomputable def stackPopSuccessPost (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  let post := emptyLocalsHOLFinite (stackPopStored s frame sp)
  { post with locals := (HolFiniteMapExact.resVarEq post.locals
      (ofString "sp", s.locals.lookup (ofString "sp"))) }

/-- The finite map bound by a one-word `charge_gas` call. -/
noncomputable def chargeGasCallee (amount : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  HolFiniteMapExact.empty.update (ofString "amount", .val (.word amount))

/-- The finite map bound by a two-value `u256_add` call. -/
noncomputable def u256AddCallee (a b : ValueHOL 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "a", a)).update (ofString "b", b)

/-- The finite map bound by a one-value `stack_push` call. -/
noncomputable def stackPushCallee (v : ValueHOL 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  HolFiniteMapExact.empty.update (ofString "v", v)

/-- The finite map bound by a one-word `pc_add` call. -/
noncomputable def pcAddCallee (n : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  HolFiniteMapExact.empty.update (ofString "n", .val (.word n))

/-- The post state of one `pc_add` body run at `value + 1`. -/
noncomputable def pcAddSuccessPost (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame value : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  emptyLocalsHOLFinite { s with memory := writeWordMemory s (frame + 0) (value + 1) }

/-- The number of words copied when restoring a previous local binding. -/
def oldBindingWords (s : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlStringHOL) : Nat :=
  ((s.locals.lookup name).map (fun old => (flattenHOL old).length)).getD 0

/-- The result limbs of the installed four-limb add. -/
def opAddLimb0 (a0 b0 : BitVec 64) : BitVec 64 := u256AddCarryResult a0 b0 0
def opAddLimb1 (a0 a1 b0 b1 : BitVec 64) : BitVec 64 :=
  u256AddCarryResult a1 b1 (u256AddCarryOverflow a0 b0 0)
def opAddLimb2 (a0 a1 a2 b0 b1 b2 : BitVec 64) : BitVec 64 :=
  u256AddCarryResult a2 b2 (u256AddCarryOverflow a1 b1 (u256AddCarryOverflow a0 b0 0))
def opAddLimb3 (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : BitVec 64 :=
  u256AddCarryResult a3 b3
    (u256AddCarryOverflow a2 b2 (u256AddCarryOverflow a1 b1 (u256AddCarryOverflow a0 b0 0)))

/-- The four-limb result value returned by `u256_add`. -/
noncomputable def opAddRValue (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : ValueHOL 64 :=
  fourWordValue (opAddLimb0 a0 b0) (opAddLimb1 a0 a1 b0 b1)
    (opAddLimb2 a0 a1 a2 b0 b1 b2) (opAddLimb3 a0 a1 a2 a3 b0 b1 b2 b3)

/-- Continuation state after the first pop has bound `x`. -/
noncomputable def opAddXEntry (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x : ValueHOL 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  setVarHOLFinite (ofString "x") x
    { stackPopSuccessPost (callEntryStateHOLFinite s HolFiniteMapExact.empty) frame sp
      with locals := s.locals }

/-- Continuation state after the second pop has bound `y`. -/
noncomputable def opAddYEntry (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  let sX := opAddXEntry s frame sp x
  setVarHOLFinite (ofString "y") y
    { stackPopSuccessPost (callEntryStateHOLFinite sX HolFiniteMapExact.empty) frame (sp - 1)
      with locals := sX.locals }

/-- Post state of the `charge_gas` call, after its returned word was discarded
and the caller's locals were restored. -/
noncomputable def opAddGasState (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  let sY := opAddYEntry s frame sp x y
  { chargeGasPost (callEntryStateHOLFinite sY (chargeGasCallee 3)) frame
      funding.left funding.used 3 with locals := sY.locals }

/-- Continuation state after `u256_add` has bound `r`. -/
noncomputable def opAddREntry (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  let sZ := opAddGasState s frame sp x y funding
  setVarHOLFinite (ofString "r") (opAddRValue a0 a1 a2 a3 b0 b1 b2 b3)
    { u256AddPost (callEntryStateHOLFinite sZ (u256AddCallee x y)) a0 a1 a2 a3 b0 b1 b2 b3
      with locals := sZ.locals }

/-- Post state of the `stack_push` call, after its returned word was discarded
and the caller's locals were restored. -/
noncomputable def opAddPushState (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  let sR := opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3
  let rv := opAddRValue a0 a1 a2 a3 b0 b1 b2 b3
  { stackPushPost (callEntryStateHOLFinite sR (stackPushCallee rv)) frame (sp - 2) cap base
      (opAddLimb0 a0 b0) (opAddLimb1 a0 a1 b0 b1) (opAddLimb2 a0 a1 a2 b0 b1 b2)
      (opAddLimb3 a0 a1 a2 a3 b0 b1 b2 b3) with locals := sR.locals }

/-- Post state of the `pc_add` call, after its returned word was discarded and
the caller's locals were restored. -/
noncomputable def opAddPcState (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  let sP := opAddPushState s frame sp cap base x y funding a0 a1 a2 a3 b0 b1 b2 b3
  { emptyLocalsHOLFinite
      { callEntryStateHOLFinite sP (pcAddCallee 1) with
        memory := writeWordMemory sP (frame + 0) (pc + 1) }
    with locals := sP.locals }

/-- Final post of the executed `op_add` body: the `return 0` clears the locals
and each declared call restores the caller's previous binding. -/
noncomputable def opAddFinalPost (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  let sZ := opAddGasState s frame sp x y funding
  let sPc := opAddPcState s frame sp cap base pc x y funding a0 a1 a2 a3 b0 b1 b2 b3
  let postR := emptyLocalsHOLFinite sPc
  let postR := { postR with locals := (HolFiniteMapExact.resVarEq postR.locals
    (ofString "r", sZ.locals.lookup (ofString "r"))) }
  let sX := opAddXEntry s frame sp x
  let postY := { postR with locals := (HolFiniteMapExact.resVarEq postR.locals
    (ofString "y", sX.locals.lookup (ofString "y"))) }
  { postY with locals := (HolFiniteMapExact.resVarEq postY.locals
    (ofString "x", s.locals.lookup (ofString "x"))) }


/-- The exact same work-event trace executed by the installed `op_add` arm:
both popping calls, the `charge_gas` call, the four-limb `u256_add` call, the
`stack_push` call, the `pc_add` call and `return 0`, each wrapped with the
actual argument/return/frame/old-binding events recorded by the call rules. -/
noncomputable def opAddEvents (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : List WorkEvent :=
  let xv : ValueHOL 64 := fourWordValue a0 a1 a2 a3
  let yv : ValueHOL 64 := fourWordValue b0 b1 b2 b3
  let rv : ValueHOL 64 := opAddRValue a0 a1 a2 a3 b0 b1 b2 b3
  let sX := opAddXEntry s frame sp xv
  let sY := opAddYEntry s frame sp xv yv
  let sZ := opAddGasState s frame sp xv yv funding
  let sR := opAddREntry s frame sp xv yv funding a0 a1 a2 a3 b0 b1 b2 b3
  let sP := opAddPushState s frame sp cap base xv yv funding a0 a1 a2 a3 b0 b1 b2 b3
  let sPc := opAddPcState s frame sp cap base pc xv yv funding a0 a1 a2 a3 b0 b1 b2 b3
  decCallEvents s [] [] comb4Shape
    (stackPopSuccessEvents (callEntryStateHOLFinite s HolFiniteMapExact.empty)
      frame sp (base + (sp - 1) * 32) a0 a1 a2 a3)
    xv
    (decCallEvents sX [] [] comb4Shape
      (stackPopSuccessEvents (callEntryStateHOLFinite sX HolFiniteMapExact.empty)
        frame (sp - 1) (base + (sp - 1 - 1) * 32) b0 b1 b2 b3)
      yv
      (callEvents sY [.const (3 : BitVec 64)] [.val (.word 3)] .one
        (some (.returned (.val (.word 0))))
        (chargeGasBodyEvents (callEntryStateHOLFinite sY (chargeGasCallee 3)) frame
          funding.left funding.used 3) (some (none, none)) ++
       decCallEvents sZ
        [.var VarKind.local (ofString "x"), .var VarKind.local (ofString "y")] [xv, yv]
        comb4Shape
        (u256AddEvents (callEntryStateHOLFinite sZ (u256AddCallee xv yv))
          a0 a1 a2 a3 b0 b1 b2 b3)
        rv
        (callEvents sR [.var VarKind.local (ofString "r")] [rv] .one
          (some (.returned (.val (.word 0))))
          (stackPushSuccessEvents (callEntryStateHOLFinite sR (stackPushCallee rv))
            frame (sp - 2) cap base (opAddLimb0 a0 b0) (opAddLimb1 a0 a1 b0 b1)
            (opAddLimb2 a0 a1 a2 b0 b1 b2) (opAddLimb3 a0 a1 a2 a3 b0 b1 b2 b3)) (some (none, none)) ++
         callEvents sP [.const (1 : BitVec 64)] [.val (.word 1)] .one
          (some (.returned (.val (.word 0))))
          (pcAddEvents (callEntryStateHOLFinite sP (pcAddCallee 1)) frame pc 1) (some (none, none)) ++
         (.statement :: (expressionEvents sPc (.const (0 : BitVec 64)) ++
           [.cost (returnOverhead (flattenHOL (.val (.word (0 : BitVec 64)))).length)])))
        (oldBindingWords sZ (ofString "r")))
      (oldBindingWords sX (ofString "y")))
    (oldBindingWords s (ofString "x"))


/-- Exact local price of the same `op_add` trace: the seven executed statements
(three `decCall`/`call` entries, the two inner calls, and `return 0`), the
evaluated argument expressions, the copied argument/return/old-binding words,
the declared-shape and argument frame slots, and the four traced callee bodies.
Every term is a coefficient times a size actually recorded in the trace. -/
noncomputable def opAddLocalCost (coeff : Work) (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : Nat :=
  coeff.score (executionWork
    (opAddEvents s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3))
theorem opAdd_body_run
    (coeff : Work)
    (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (installed : s.code.lookup = originalRuntimeCode.lookup)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (clock0 : s.clock ≠ 0)
    (spDomain : s.memaddrs (frame + 16)) (spCell : s.memory (frame + 16) = .word sp)
    (nonzero : sp ≠ 0)
    (baseDomain : s.memaddrs (frame + 8)) (baseCell : s.memory (frame + 8) = .word base)
    (xDomain0 : (stackPopStored s frame sp).memaddrs (base + (sp - 1) * 32))
    (xDomain1 : (stackPopStored s frame sp).memaddrs (base + (sp - 1) * 32 + 8))
    (xDomain2 : (stackPopStored s frame sp).memaddrs (base + (sp - 1) * 32 + 16))
    (xDomain3 : (stackPopStored s frame sp).memaddrs (base + (sp - 1) * 32 + 24))
    (xCell0 : (stackPopStored s frame sp).memory (base + (sp - 1) * 32) = .word a0)
    (xCell1 : (stackPopStored s frame sp).memory (base + (sp - 1) * 32 + 8) = .word a1)
    (xCell2 : (stackPopStored s frame sp).memory (base + (sp - 1) * 32 + 16) = .word a2)
    (xCell3 : (stackPopStored s frame sp).memory (base + (sp - 1) * 32 + 24) = .word a3)
    (clockX : (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)).clock ≠ 0)
    (nonzeroY : (sp - 1) ≠ 0)
    (spYDomain : (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)).memaddrs (frame + 16))
    (spYCell : (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)).memory (frame + 16) =
      .word (sp - 1))
    (baseYDomain : (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)).memaddrs (frame + 8))
    (baseYCell : (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)).memory (frame + 8) =
      .word base)
    (yDomain0 : (stackPopStored (callEntryStateHOLFinite
      (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty)
      frame (sp - 1)).memaddrs (base + (sp - 1 - 1) * 32))
    (yDomain1 : (stackPopStored (callEntryStateHOLFinite
      (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty)
      frame (sp - 1)).memaddrs (base + (sp - 1 - 1) * 32 + 8))
    (yDomain2 : (stackPopStored (callEntryStateHOLFinite
      (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty)
      frame (sp - 1)).memaddrs (base + (sp - 1 - 1) * 32 + 16))
    (yDomain3 : (stackPopStored (callEntryStateHOLFinite
      (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty)
      frame (sp - 1)).memaddrs (base + (sp - 1 - 1) * 32 + 24))
    (yCell0 : (stackPopStored (callEntryStateHOLFinite
      (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty)
      frame (sp - 1)).memory (base + (sp - 1 - 1) * 32) = .word b0)
    (yCell1 : (stackPopStored (callEntryStateHOLFinite
      (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty)
      frame (sp - 1)).memory (base + (sp - 1 - 1) * 32 + 8) = .word b1)
    (yCell2 : (stackPopStored (callEntryStateHOLFinite
      (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty)
      frame (sp - 1)).memory (base + (sp - 1 - 1) * 32 + 16) = .word b2)
    (yCell3 : (stackPopStored (callEntryStateHOLFinite
      (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty)
      frame (sp - 1)).memory (base + (sp - 1 - 1) * 32 + 24) = .word b3)
    (clockY : (opAddYEntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3)).clock ≠ 0)
    (fundingY : HasGasFunding (opAddYEntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3)) frame funding)
    (enough : (3 : BitVec 64) ≤ funding.left)
    (gasLeftDomain : (opAddYEntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3)).memaddrs (frame + 64))
    (gasUsedDomain : (opAddYEntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3)).memaddrs (frame + 184))
    (clockZ : (opAddGasState s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding).clock ≠ 0)
    (clockR : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).clock ≠ 0)
    (pushSpDomain : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (frame + 16))
    (pushSpCell : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 16) =
      .word (sp - 2))
    (capDomain : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (frame + 232))
    (capCell : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 232) =
      .word cap)
    (pushBaseDomain : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (frame + 8))
    (pushBaseCell : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 8) =
      .word base)
    (below : (sp - 2).toNat < cap.toNat)
    (notFull : (sp - 2) ≠ (1024 : BitVec 64))
    (storeDomain0 : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs
      (base + (sp - 2) * 32))
    (storeDomain1 : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs
      (base + (sp - 2) * 32 + 8))
    (storeDomain2 : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs
      (base + (sp - 2) * 32 + 8 + 8))
    (storeDomain3 : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs
      (base + (sp - 2) * 32 + 8 + 8 + 8))
    (clockP : (opAddPushState s frame sp cap base (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).clock ≠ 0)
    (pcDomain : (opAddPushState s frame sp cap base (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (frame + 0))
    (pcCell : (opAddPushState s frame sp cap base (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 0) =
      .word pc) :
    StatementRun s (sourceFunctionBody Guest.guestFn_op_add)
      (some (.returned (.val (.word 0))))
      (opAddFinalPost s frame sp cap base pc (fourWordValue a0 a1 a2 a3)
        (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3)
      (opAddEvents s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3) := by
  classical
  let xv : ValueHOL 64 := fourWordValue a0 a1 a2 a3
  let yv : ValueHOL 64 := fourWordValue b0 b1 b2 b3
  let rv : ValueHOL 64 := opAddRValue a0 a1 a2 a3 b0 b1 b2 b3
  let sX := opAddXEntry s frame sp xv
  let sY := opAddYEntry s frame sp xv yv
  let sZ := opAddGasState s frame sp xv yv funding
  let sR := opAddREntry s frame sp xv yv funding a0 a1 a2 a3 b0 b1 b2 b3
  let sP := opAddPushState s frame sp cap base xv yv funding a0 a1 a2 a3 b0 b1 b2 b3
  let sPc := opAddPcState s frame sp cap base pc xv yv funding a0 a1 a2 a3 b0 b1 b2 b3
  have globalsX : sX.globals = s.globals := rfl
  have globalsY : sY.globals = s.globals := rfl
  have globalsZ : sZ.globals = s.globals := rfl
  have globalsR : sR.globals = s.globals := rfl
  have globalsP : sP.globals = s.globals := rfl
  have memaddrsX : sX.memaddrs = s.memaddrs := rfl
  have memaddrsY : sY.memaddrs = s.memaddrs := rfl
  have memaddrsZ : sZ.memaddrs = s.memaddrs := rfl
  have memaddrsR : sR.memaddrs = s.memaddrs := rfl
  have memaddrsP : sP.memaddrs = s.memaddrs := rfl
  have xShape : (shapeEqHOL (shapeOfHOLExact xv) comb4Shape &&
      shapeEqHOL (shapeOfHOLExact xv) comb4Shape) = true := by
    simp [xv, fourWordValue, comb4Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
  have yShape : (shapeEqHOL (shapeOfHOLExact yv) comb4Shape &&
      shapeEqHOL (shapeOfHOLExact yv) comb4Shape) = true := by
    simp [yv, fourWordValue, comb4Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
  have rShape : (shapeEqHOL (shapeOfHOLExact rv) comb4Shape &&
      shapeEqHOL (shapeOfHOLExact rv) comb4Shape) = true := by
    simp [rv, opAddRValue, fourWordValue, comb4Shape, shapeOfHOLExact, shapeEqHOL,
      shapeEqHOL.shapeEqListHOL]
  -- the outer return 0
  have retRun : StatementRun sPc (.return (.const 0)) (some (.returned (.val (.word 0))))
      (emptyLocalsHOLFinite sPc)
      (.statement :: (expressionEvents sPc (.const 0) ++
        [.cost (returnOverhead (flattenHOL (.val (.word (0 : BitVec 64)))).length)])) :=
    StatementRun.returnValue (expression := .const (0 : BitVec 64))
      (costedExpression_events sPc _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  -- the pc_add call
  have pcArgs : evalListHOLFinite sP (h := fun a => Classical.propDecidable (sP.memaddrs a))
      [.const (1 : BitVec 64)] = some [.val (.word 1)] :=
    evalListHOLFinite_singleton_const sP 1
  have pcLookup : lookupCodeHOLFinite sP.code.lookup (ofString "pc_add") [.val (.word 1)] =
      some (sourceFunctionBody Guest.guestFn_pc_add, pcAddCallee 1, .one) := by
    simpa [pcAddCallee] using opAdd_pcAdd_lookup sP.code.lookup installed 1
  have pcBody : StatementRun (callEntryStateHOLFinite sP (pcAddCallee 1))
      (sourceFunctionBody Guest.guestFn_pc_add) (some (.returned (.val (.word 0))))
      (pcAddSuccessPost (callEntryStateHOLFinite sP (pcAddCallee 1)) frame pc)
      (pcAddEvents (callEntryStateHOLFinite sP (pcAddCallee 1)) frame pc 1) := by
    have := pcAdd_run (callEntryStateHOLFinite sP (pcAddCallee 1)) frame pc 1
      hFrame
      (by simp [callEntryStateHOLFinite, pcAddCallee, HolFiniteMapExact.lookup_update, FUPDATE])
      pcDomain pcCell
    simpa [pcAddSuccessPost] using this
  have pcPlan : callCostPlan sP (some (none, none)) .one
      (some (.returned (.val (.word 0)))) (pcAddSuccessPost
        (callEntryStateHOLFinite sP (pcAddCallee 1)) frame pc) =
      .done none sPc := by
    rw [callCostPlan_discard_word _ _]
    rfl
  have pcCall := (call_statement_work (coeff := coeff) pcArgs pcLookup clockP pcBody pcPlan).1
  have pcSeq := StatementRun.seqNext pcCall retRun
  -- the stack_push call
  have pushArgs : evalListHOLFinite sR (h := fun a => Classical.propDecidable (sR.memaddrs a))
      [.var VarKind.local (ofString "r")] = some [rv] := by
    apply evalListHOLFinite_singleton_var
    simp [sR, opAddREntry, setVarHOLFinite, FUPDATE, rv]
  have pushLookup : lookupCodeHOLFinite sR.code.lookup (ofString "stack_push") [rv] =
      some (sourceFunctionBody Guest.guestFn_stack_push, stackPushCallee rv, .one) := by
    simpa [stackPushCallee] using opAdd_stackPush_lookup sR.code.lookup installed rv
      (by simp [rv, opAddRValue, fourWordValue, comb4Shape, shapeOfHOLExact, shapeEqHOL,
        shapeEqHOL.shapeEqListHOL])
  have pushBody : StatementRun (callEntryStateHOLFinite sR (stackPushCallee rv))
      (sourceFunctionBody Guest.guestFn_stack_push) (some (.returned (.val (.word 0))))
      (stackPushPost (callEntryStateHOLFinite sR (stackPushCallee rv)) frame (sp - 2) cap base
        (opAddLimb0 a0 b0) (opAddLimb1 a0 a1 b0 b1) (opAddLimb2 a0 a1 a2 b0 b1 b2)
        (opAddLimb3 a0 a1 a2 a3 b0 b1 b2 b3))
      (stackPushSuccessEvents (callEntryStateHOLFinite sR (stackPushCallee rv)) frame (sp - 2)
        cap base (opAddLimb0 a0 b0) (opAddLimb1 a0 a1 b0 b1) (opAddLimb2 a0 a1 a2 b0 b1 b2)
        (opAddLimb3 a0 a1 a2 a3 b0 b1 b2 b3)) := by
    have hV : (callEntryStateHOLFinite sR (stackPushCallee rv)).locals.lookup
        (ofString "v") = some (fourWordValue
          (opAddLimb0 a0 b0) (opAddLimb1 a0 a1 b0 b1) (opAddLimb2 a0 a1 a2 b0 b1 b2)
          (opAddLimb3 a0 a1 a2 a3 b0 b1 b2 b3)) := by
      simp [callEntryStateHOLFinite, stackPushCallee, rv, opAddRValue, fourWordValue,
        HolFiniteMapExact.lookup_update, FUPDATE]
    have := stackPush_success_run (F := Guest.HostMemory)
      (s := callEntryStateHOLFinite sR (stackPushCallee rv))
      frame (sp - 2) cap base (opAddLimb0 a0 b0) (opAddLimb1 a0 a1 b0 b1)
      (opAddLimb2 a0 a1 a2 b0 b1 b2) (opAddLimb3 a0 a1 a2 a3 b0 b1 b2 b3)
      hFrame pushSpDomain pushSpCell capDomain capCell hV pushBaseDomain pushBaseCell
      below notFull storeDomain0 storeDomain1 storeDomain2 storeDomain3
    simpa using this
  have pushPlan : callCostPlan sR (some (none, none)) .one
      (some (.returned (.val (.word 0)))) (stackPushPost
        (callEntryStateHOLFinite sR (stackPushCallee rv)) frame (sp - 2) cap base
        (opAddLimb0 a0 b0) (opAddLimb1 a0 a1 b0 b1) (opAddLimb2 a0 a1 a2 b0 b1 b2)
        (opAddLimb3 a0 a1 a2 a3 b0 b1 b2 b3)) = .done none sP := by
    rw [callCostPlan_discard_word _ _]
    rfl
  have pushCall := (call_statement_work (coeff := coeff) pushArgs pushLookup clockR
    pushBody pushPlan).1
  have pushSeq := StatementRun.seqNext pushCall pcSeq
  -- the u256_add decCall
  have rArgs : evalListHOLFinite sZ (h := fun a => Classical.propDecidable (sZ.memaddrs a))
      [.var VarKind.local (ofString "x"), .var VarKind.local (ofString "y")] =
      some [xv, yv] := by
    apply evalListHOLFinite_two_vars
    · simp [sZ, sY, opAddGasState, opAddYEntry, opAddXEntry, setVarHOLFinite, FUPDATE,
        (by decide_cbv : (ofString "y" : MlStringHOL) ≠ ofString "x"),
        (by decide_cbv : (ofString "x" : MlStringHOL) ≠ ofString "y")]
    · simp [sZ, sY, opAddGasState, opAddYEntry, opAddXEntry, setVarHOLFinite, FUPDATE,
        (by decide_cbv : (ofString "y" : MlStringHOL) ≠ ofString "x"),
        (by decide_cbv : (ofString "x" : MlStringHOL) ≠ ofString "y")]
  have rLookup : lookupCodeHOLFinite sZ.code.lookup (ofString "u256_add") [xv, yv] =
      some (sourceFunctionBody Guest.guestFn_u256_add, u256AddCallee xv yv, comb4Shape) := by
    simpa [u256AddCallee] using opAdd_u256Add_lookup sZ.code.lookup installed xv yv
      (by simpa [xv] using fourWordValue_shape a0 a1 a2 a3)
      (by simpa [yv] using fourWordValue_shape b0 b1 b2 b3)
  have rBody : StatementRun (callEntryStateHOLFinite sZ (u256AddCallee xv yv))
      (sourceFunctionBody Guest.guestFn_u256_add) (some (.returned rv))
      (u256AddPost (callEntryStateHOLFinite sZ (u256AddCallee xv yv))
        a0 a1 a2 a3 b0 b1 b2 b3)
      (u256AddEvents (callEntryStateHOLFinite sZ (u256AddCallee xv yv))
        a0 a1 a2 a3 b0 b1 b2 b3) := by
    have hA : (callEntryStateHOLFinite sZ (u256AddCallee xv yv)).locals.lookup
        (ofString "a") = some (fourWordValue a0 a1 a2 a3) := by
      simp [callEntryStateHOLFinite, u256AddCallee, HolFiniteMapExact.lookup_update_pointwise,
        FUPDATE, xv, fourWordValue,
        show (ofString "a" : MlStringHOL) ≠ ofString "b" by decide,
        show (ofString "b" : MlStringHOL) ≠ ofString "a" by decide]
    have hB : (callEntryStateHOLFinite sZ (u256AddCallee xv yv)).locals.lookup
        (ofString "b") = some (fourWordValue b0 b1 b2 b3) := by
      simp [callEntryStateHOLFinite, u256AddCallee, HolFiniteMapExact.lookup_update_pointwise,
        FUPDATE, yv, fourWordValue,
        show (ofString "b" : MlStringHOL) ≠ ofString "a" by decide,
        show (ofString "a" : MlStringHOL) ≠ ofString "b" by decide]
    have := u256Add_run (F := Guest.HostMemory)
      (s := callEntryStateHOLFinite sZ (u256AddCallee xv yv))
      a0 a1 a2 a3 b0 b1 b2 b3 hA hB
    simpa [rv, opAddRValue, opAddLimb0, opAddLimb1, opAddLimb2, opAddLimb3, fourWordValue] using this
  have rRun := (decCall_statement_work (coeff := coeff) (name := ofString "r")
    (shape := comb4Shape) (function := ofString "u256_add")
    (arguments := [.var VarKind.local (ofString "x"), .var VarKind.local (ofString "y")])
    (continuation := (.seq (.call (some (none, none)) (ofString "stack_push")
        [(.var VarKind.local (ofString "r"))])
      (.seq (.call (some (none, none)) (ofString "pc_add") [(.const (1 : BitVec 64))])
        (.return (.const (0 : BitVec 64))))))
    (values := [xv, yv]) rArgs rLookup clockZ rBody rShape pushSeq (oldWords := oldBindingWords sZ (ofString "r")) rfl).1
  -- the charge_gas call
  have gasArgs : evalListHOLFinite sY (h := fun a => Classical.propDecidable (sY.memaddrs a))
      [.const (3 : BitVec 64)] = some [.val (.word 3)] :=
    evalListHOLFinite_singleton_const sY 3
  have gasLookup : lookupCodeHOLFinite sY.code.lookup (ofString "charge_gas") [.val (.word 3)] =
      some (sourceFunctionBody Guest.guestFn_charge_gas, chargeGasCallee 3, .one) := by
    simpa [chargeGasCallee] using opAdd_chargeGas_lookup sY.code.lookup installed 3
  have gasBody : StatementRun (callEntryStateHOLFinite sY (chargeGasCallee 3))
      (sourceFunctionBody Guest.guestFn_charge_gas) (some (.returned (.val (.word 0))))
      (chargeGasPost (callEntryStateHOLFinite sY (chargeGasCallee 3)) frame
        funding.left funding.used 3)
      (chargeGasBodyEvents (callEntryStateHOLFinite sY (chargeGasCallee 3)) frame
        funding.left funding.used 3) := by
    have := chargeGas_body_run_funding (state := callEntryStateHOLFinite sY (chargeGasCallee 3))
      frame 3 funding
      hFrame
      (by simp [callEntryStateHOLFinite, chargeGasCallee, HolFiniteMapExact.lookup_update, FUPDATE])
      gasLeftDomain gasUsedDomain fundingY enough
    simpa using this
  have gasPlan : callCostPlan sY (some (none, none)) .one
      (some (.returned (.val (.word 0))))
      (chargeGasPost (callEntryStateHOLFinite sY (chargeGasCallee 3)) frame
        funding.left funding.used 3) = .done none sZ := by
    rw [callCostPlan_discard_word _ _]
    rfl
  have gasCall := (call_statement_work (coeff := coeff) gasArgs gasLookup clockY
    gasBody gasPlan).1
  have gasSeq := StatementRun.seqNext gasCall rRun
  -- the second pop decCall
  have yArgs : evalListHOLFinite sX (h := fun a => Classical.propDecidable (sX.memaddrs a))
      [] = some [] := evalListHOLFinite_nil sX
  have yLookup : lookupCodeHOLFinite sX.code.lookup (ofString "stack_pop") [] =
      some (sourceFunctionBody Guest.guestFn_stack_pop, HolFiniteMapExact.empty, comb4Shape) :=
    opAdd_stackPop_lookup sX.code.lookup installed
  have yBody : StatementRun (callEntryStateHOLFinite sX HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_stack_pop) (some (.returned yv))
      (stackPopSuccessPost (callEntryStateHOLFinite sX HolFiniteMapExact.empty) frame (sp - 1))
      (stackPopSuccessEvents (callEntryStateHOLFinite sX HolFiniteMapExact.empty)
        frame (sp - 1) (base + (sp - 1 - 1) * 32) b0 b1 b2 b3) := by
    have := stackPop_success_run (F := Guest.HostMemory)
      (state := callEntryStateHOLFinite sX HolFiniteMapExact.empty)
      frame (sp - 1) base b0 b1 b2 b3
      hFrame spYDomain spYCell nonzeroY baseYDomain baseYCell
      yDomain0 yDomain1 yDomain2 yDomain3 yCell0 yCell1 yCell2 yCell3
    simpa [yv, fourWordValue, stackPopSuccessPost] using this
  have yRun := (decCall_statement_work (coeff := coeff) (name := ofString "y")
    (shape := comb4Shape) (function := ofString "stack_pop") (arguments := [])
    (continuation := (.seq (.call (some (none, none)) (ofString "charge_gas")
        [(.const (3 : BitVec 64))])
      (.decCall (ofString "r") comb4Shape (ofString "u256_add")
        [(.var VarKind.local (ofString "x")), (.var VarKind.local (ofString "y"))]
        (.seq (.call (some (none, none)) (ofString "stack_push")
            [(.var VarKind.local (ofString "r"))])
          (.seq (.call (some (none, none)) (ofString "pc_add") [(.const (1 : BitVec 64))])
            (.return (.const (0 : BitVec 64))))))))
    (values := []) yArgs yLookup clockX yBody yShape gasSeq (oldWords := oldBindingWords sX (ofString "y")) rfl).1
  -- the first pop decCall
  have xArgs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [] = some [] := evalListHOLFinite_nil s
  have xLookup : lookupCodeHOLFinite s.code.lookup (ofString "stack_pop") [] =
      some (sourceFunctionBody Guest.guestFn_stack_pop, HolFiniteMapExact.empty, comb4Shape) :=
    opAdd_stackPop_lookup s.code.lookup installed
  have xBody : StatementRun (callEntryStateHOLFinite s HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_stack_pop) (some (.returned xv))
      (stackPopSuccessPost (callEntryStateHOLFinite s HolFiniteMapExact.empty) frame sp)
      (stackPopSuccessEvents (callEntryStateHOLFinite s HolFiniteMapExact.empty)
        frame sp (base + (sp - 1) * 32) a0 a1 a2 a3) := by
    have := stackPop_success_run (F := Guest.HostMemory)
      (state := callEntryStateHOLFinite s HolFiniteMapExact.empty) frame sp base a0 a1 a2 a3
      hFrame spDomain spCell nonzero baseDomain baseCell
      xDomain0 xDomain1 xDomain2 xDomain3 xCell0 xCell1 xCell2 xCell3
    simpa [xv, fourWordValue, stackPopSuccessPost] using this
  have xRun := (decCall_statement_work (coeff := coeff) (name := ofString "x")
    (shape := comb4Shape) (function := ofString "stack_pop") (arguments := [])
    (continuation := (.decCall (ofString "y") comb4Shape (ofString "stack_pop") []
      (.seq (.call (some (none, none)) (ofString "charge_gas") [(.const (3 : BitVec 64))])
        (.decCall (ofString "r") comb4Shape (ofString "u256_add")
          [(.var VarKind.local (ofString "x")), (.var VarKind.local (ofString "y"))]
          (.seq (.call (some (none, none)) (ofString "stack_push")
              [(.var VarKind.local (ofString "r"))])
            (.seq (.call (some (none, none)) (ofString "pc_add") [(.const (1 : BitVec 64))])
              (.return (.const (0 : BitVec 64)))))))))
    (values := []) xArgs xLookup clock0 xBody xShape yRun (oldWords := oldBindingWords s (ofString "x")) rfl).1
  rw [source_opAdd_body]
  simpa [opAddFinalPost, opAddEvents, opAddSpine, sX, sY, sZ, sR, sP, sPc, xv, yv, rv] using xRun



/-- Closed price of the actual `op_add` trace: the same event vector scores
exactly the recursively composed local cost. -/
theorem opAddEvents_score (coeff : Work) (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    coeff.score (executionWork (opAddEvents s frame sp cap base pc funding
      a0 a1 a2 a3 b0 b1 b2 b3)) =
      opAddLocalCost coeff s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3 := by
  rfl

#print axioms opAddEvents_score

/-- The state defs are concrete: the pushed limbs are the limb results. -/
theorem opAddRValue_shape (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    shapeEqHOL comb4Shape
      (shapeOfHOLExact (opAddRValue a0 a1 a2 a3 b0 b1 b2 b3)) = true :=
  fourWordValue_shape _ _ _ _

#print axioms opAddRValue_shape
end InitECandidate.Runtime.FineCost
