import InitECandidate.Runtime.MemoryExtensionSource
import InitECandidate.Runtime.MemzeroCallBound
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def memoryExtensionZeroCost : Nat:=33806089496/32+33806089496/8+11
/-- Uniform budget for the actual final zeroing/store/return suffix. Every
memory-error outcome is included; no successful zeroing/readability assumed. -/
theorem memory_extension_final_suffix_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame base length expansion : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atLength : s.locals.lookup (ofString "len")=some (.val (.word length)))
 (atExpansion : s.locals.lookup (ofString "expand_by")=some (.val (.word expansion)))
 (baseDomain : s.memaddrs (frame+24)) (baseAt : s.memory (frame+24)=.word base)
 (small : expansion.toNat≤33806089496) (code : s.code=originalRuntimeCode)
 (budget : memoryExtensionZeroCost≤s.clock) :
 RunBounded s (memoryExtensionAt 5) memoryExtensionZeroCost := by
 have loaded:=eval_fundingLoad s frame (24#64) base atFrame baseDomain baseAt
 change @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (.load .one (fundingAddress (24#64)))=some (.val (.word base)) at loaded
 have destination : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .add [.load .one (fundingAddress (24#64)),.var .local (ofString "len")])=some (.val (.word (base+length))) := by
  rw [evalHOLExact,evalListHOLExact,loaded]
  simp [evalListHOLExact,evalHOLExact,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.op .add [.load .one (fundingAddress 24),.var .local (ofString "len")],.var .local (ofString "expand_by")]=some [.val (.word (base+length)),.val (.word expansion)] := by
  change @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) [.op .add [.load .one (fundingAddress (24#64)),.var .local (ofString "len")],.var .local (ofString "expand_by")]=_
  rw [evalListHOLFinite,evalListHOLExact,destination]
  simp [evalListHOLExact,evalHOLExact,atExpansion]
 have cost : expansion.toNat/32+expansion.toNat/8+11≤memoryExtensionZeroCost := by
  unfold memoryExtensionZeroCost
  have a:=Nat.div_le_div_right (c:=32) small
  have b:=Nat.div_le_div_right (c:=8) small
  omega
 have zero : RunBounded s (.call (some (none,none)) (ofString "memzero") [.op .add [.load .one (fundingAddress 24),.var .local (ofString "len")],.var .local (ofString "expand_by")]) memoryExtensionZeroCost :=
  RunBounded.weaken (evaluate_memzero_call_bounded s _ (base+length) expansion args code small (by omega)) cost
 rw [source_memory_extension_5]
 have result:=RunBounded.seq zero (b:=0) (by omega) (by
  intro next ran installed remaining
  exact RunBounded.ofProg (ProgBounded.straight (memoryExtensionAt 6) (by decide_cbv)) (installed.trans code) (by omega))
 simpa only [Nat.add_zero] using result
#print axioms memory_extension_final_suffix_bounded
end InitECandidate.Runtime
