import InitECandidate.Runtime.SecpInitBlockCall
import InitECandidate.Runtime.AllocationGlobalCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 2000000

/-- The secp256k1 field prime p and group order n as four little-endian words. -/
def secpP : List (BitVec 64) := [18446744069414583343,18446744073709551615,18446744073709551615,18446744073709551615]
def secpN : List (BitVec 64) := [13822214165235122497,13451932020343611451,18446744073709551614,18446744073709551615]

/-- Memory after the first secp256k1 initialization from scratch arena `base`. -/
def secpInitMemory (memory : BitVec 64 → HolWordLab 64) (base : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  memWrites (memWrites memory base
      (secpBlockCells 18446744069414583343 18446744073709551615 18446744073709551615 18446744073709551615))
    (base + 160) (secpBlockCells 13822214165235122497 13451932020343611451 18446744073709551614 18446744073709551615)

/-- First (uninitialized) secp256k1_init: allocates the 448-byte accelerator
arena at the current heap pointer, records it in secp_accel_scratch, installs
c = 0 and the moduli p and n, and returns 0 after three ticks. -/
theorem evaluate_secp256k1Init_body_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0)))
    (request : (448 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 448).toNat ≤ 33806089496)
    (domainP : ∀ cell ∈ secpBlockCells 18446744069414583343 18446744073709551615 18446744073709551615 18446744073709551615,
      state.memaddrs (pointer + cell.1))
    (domainN : ∀ cell ∈ secpBlockCells 13822214165235122497 13451932020343611451 18446744073709551614 18446744073709551615,
      state.memaddrs (pointer + 160 + cell.1))
    (budget : 3 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_secp256k1_init) =
        (some (.returned (.val (.word 0))),post) ∧
      post.clock = state.clock - 3 ∧ post.memory = secpInitMemory state.memory pointer ∧
      post.locals = HolFiniteMapExact.empty ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.be = state.be ∧
      post.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 448))) ∧
      (∀ watched, watched ≠ ofString "secp_accel_scratch" → watched ≠ ofString "heap_ptr" →
        post.globals.lookup watched = state.globals.lookup watched) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .notEqual (.var .global (ofString "secp_accel_scratch")) (.const 0)) = some (.val (.word 0)) := by
    simp [evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL]
  have size : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.op .add [.panop .mul [.const 2,.const 160],.const 128]] = some [.val (.word 448)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨ready,allocRun,rClock,rMemory,rLocals,rCode,rDomain,rBe,rScratch,rHeap,rOther⟩ :=
    evaluate_alloc_global_call state _ pointer 448 0 (ofString "secp_accel_scratch") size code (by omega) heap zero
      (by decide) request finishBound
  have argsP : evalListHOLFinite ready (h := fun a => Classical.propDecidable (ready.memaddrs a))
      [.op .add [.var .global (ofString "secp_accel_scratch"),.const 0],
       .rstruct [.const 18446744069414583343,.const 18446744073709551615,.const 18446744073709551615,.const 18446744073709551615]] =
      some [.val (.word pointer),.rStruct [.val (.word 18446744069414583343),.val (.word 18446744073709551615),
        .val (.word 18446744073709551615),.val (.word 18446744073709551615)]] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,rScratch,wordOpHOL,wordOp,valueIsWord,valueWord]
  have firstRun := evaluate_secpAccelInitBlock_call ready _ pointer _ _ _ _ (rCode.trans code) argsP
    (by intro cell member; rw [rDomain]; exact domainP cell member) (by omega)
  let middle : PanSemStateFiniteExact 64 F := {ready with clock := ready.clock - 1, memory := memWrites ready.memory pointer (secpBlockCells 18446744069414583343 18446744073709551615 18446744073709551615 18446744073709551615)}
  have argsN : evalListHOLFinite middle (h := fun a => Classical.propDecidable (middle.memaddrs a))
      [.op .add [.var .global (ofString "secp_accel_scratch"),.const 160],
       .rstruct [.const 13822214165235122497,.const 13451932020343611451,.const 18446744073709551614,.const 18446744073709551615]] =
      some [.val (.word (pointer + 160)),.rStruct [.val (.word 13822214165235122497),.val (.word 13451932020343611451),
        .val (.word 18446744073709551614),.val (.word 18446744073709551615)]] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,middle,rScratch,wordOpHOL,wordOp,valueIsWord,valueWord]
  have secondRun := evaluate_secpAccelInitBlock_call middle _ (pointer + 160) _ _ _ _ (rCode.trans code) argsN
    (by intro cell member; change ready.memaddrs _; rw [rDomain]; exact domainN cell member)
    (by change ready.clock - 1 ≠ 0; omega)
  let final : PanSemStateFiniteExact 64 F := {middle with clock := middle.clock - 1, memory := memWrites middle.memory (pointer + 160) (secpBlockCells 13822214165235122497 13451932020343611451 18446744073709551614 18446744073709551615)}
  have firstRun' : evaluateHOLFiniteState ready (.call (some (none,none)) (ofString "secp_accel_init_block")
      [.op .add [.var .global (ofString "secp_accel_scratch"),.const 0],
       .rstruct [.const 18446744069414583343,.const 18446744073709551615,.const 18446744073709551615,.const 18446744073709551615]]) =
      (none,middle) := firstRun
  have secondRun' : evaluateHOLFiniteState middle (.call (some (none,none)) (ofString "secp_accel_init_block")
      [.op .add [.var .global (ofString "secp_accel_scratch"),.const 160],
       .rstruct [.const 13822214165235122497,.const 13451932020343611451,.const 18446744073709551614,.const 18446744073709551615]]) =
      (none,final) := secondRun
  refine ⟨emptyLocalsHOLFinite final,?_,?_,?_,rfl,rCode,rDomain,rBe,rScratch,rHeap,rOther⟩
  · rw [source_secp256k1Init_body,evaluateHOLFiniteState_seq_line780]
    simp only [evaluateHOLFiniteState_ite,condition,if_true,evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780,allocRun]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,firstRun']
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780]
    rw [secondRun']
    dsimp only
    simp only [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
    rw [if_pos (by simp [sizeOfShapeWithContextHOL])]
  · change ready.clock - 1 - 1 = state.clock - 3
    omega
  · change memWrites (memWrites ready.memory _ _) _ _ = _
    rw [rMemory]; rfl

#print axioms evaluate_secp256k1Init_body_success
end InitECandidate.Runtime
