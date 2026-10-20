import InitECandidate.Runtime.MemzeroSeparatedMemory
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual normal memzero writes only below its concrete upper frontier,
including unaligned destinations. No fuel/domain/readability premise. -/
theorem memzero_normal_upper_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (arguments : List (ExpHOL 64)) (destination size upper : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word destination),.val (.word size)])
 (extent : destination.toNat+size.toNat≤upper.toNat) (cap : upper.toNat≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "memzero") arguments)=(none,post)) :
 (∀watched : BitVec 64,upper.toNat≤watched.toNat → post.memory watched=s.memory watched) ∧
 post.locals=s.locals ∧post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have frame (watched : BitVec 64) (above : upper.toNat≤watched.toNat) :
  post.memory watched=s.memory watched ∧post.locals=s.locals := by
  apply memzero_call_normal_separated_memory s post arguments destination size watched args code (by omega) _ run
  intro offset inside
  have offsetSmall : offset<2^64:=by omega
  have offsetNat : (BitVec.ofNat 64 offset).toNat=offset := by
   rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]
  have noWrap : destination.toNat+(BitVec.ofNat 64 offset).toNat<2^64 := by rw [offsetNat];omega
  constructor
  · intro equal
    have natural:=congrArg BitVec.toNat equal
    rw [BitVec.toNat_add_of_lt noWrap,offsetNat] at natural
    omega
  · intro equal
    have natural:=congrArg BitVec.toNat equal
    rw [byteAlign_toNat,BitVec.toNat_add_of_lt noWrap,offsetNat] at natural
    have below:=Nat.div_mul_le_self (destination.toNat+offset) 8
    omega
 have globals:=memzero_call_globals_frame arguments s code
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "memzero") arguments)
 rw [run] at globals metadata
 exact ⟨fun watched above=>(frame watched above).1,(frame upper (by omega)).2,globals,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms memzero_normal_upper_frame
end InitECandidate.Runtime
