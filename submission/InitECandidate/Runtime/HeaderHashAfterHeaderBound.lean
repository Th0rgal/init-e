import InitECandidate.Runtime.HeaderHashSource
import InitECandidate.Runtime.KeccakWideFullCallBound
import InitECandidate.Runtime.VmFn_heap_release
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def headerHashKeccakCeiling : Nat := (2^62)*20+125
def headerHashAfterHeaderCost : Nat := headerHashKeccakCeiling+1
private theorem after_hash_bounded : ProgBounded (headerHashAt 3) 1 := by
 have stage : headerHashAt 3=.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
  (headerHashAt 4) := rfl
 rw [stage]
 intro F s code budget
 simpa only [Nat.add_zero] using
  (ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight (headerHashAt 4) (by decide_cbv)) s code budget)
/-- The real hash/release tail uses the actual returned header pair. -/
theorem header_hash_after_header_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (pointer pad source length output : BitVec 64)
 (code : s.code=originalRuntimeCode)
 (atState : s.globals.lookup (ofString "keccak_st")=some (.val (.word pointer)))
 (atPad : s.globals.lookup (ofString "keccak_pad")=some (.val (.word pad)))
 (atE : s.locals.lookup (ofString "e")=some (.rStruct [.val (.word source),.val (.word length)]))
 (atOut : s.locals.lookup (ofString "out")=some (.val (.word output)))
 (small : length.toNat≤2^62) (outputAligned : output.toNat%8=0)
 (budget : headerHashAfterHeaderCost≤s.clock) :
 RunBounded s (headerHashAt 2) headerHashAfterHeaderCost := by
 let arguments : List (ExpHOL 64) := [.rfield 0 (.var .local (ofString "e")),.rfield 1 (.var .local (ofString "e")),.var .local (ofString "out")]
 have stage : headerHashAt 2=.seq (.call (some (none,none)) (ofString "keccak256") arguments) (headerHashAt 3) := rfl
 rw [stage]
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word source),.val (.word length),.val (.word output)] := by
  simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atE,atOut]
 have actual:=runBounded_keccak_wide_full_call s pointer pad source length output none arguments atState atPad args small outputAligned code
  (by unfold headerHashAfterHeaderCost headerHashKeccakCeiling at budget;omega)
 have bounded : RunBounded s (.call (some (none,none)) (ofString "keccak256") arguments) headerHashKeccakCeiling :=
  actual.weaken (by unfold headerHashKeccakCeiling;omega)
 apply RunBounded.seq bounded budget
 intro next _ installed remaining
 exact after_hash_bounded next (installed.trans code) remaining
#print axioms header_hash_after_header_bounded
end InitECandidate.Runtime
