import InitECandidate.Runtime.HtrU64AtMemoryFrame
import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Hashing an integer into a later chunk preserves the two concrete request
metadata cells, including their read domains. -/
theorem htrU64At_call_preserves_payload_requests {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (p out payload pointer length : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word p),.val (.word out)])
    (entry : RlpSliceEntry state payload (4#64) pointer length)
    (code : state.code = originalRuntimeCode) (aligned : out.toNat % 8 = 0)
    (fits : out.toNat + 32 ≤ 33806089496)
    (before : payload.toNat + 72 < out.toNat)
    (budget : 30 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "htr_u64_at") arguments) = (none,post)) :
    RlpSliceEntry post payload (4#64) pointer length := by
  have first : (payload + (64#64)).toNat = payload.toNat + 64 := by
    apply BitVec.toNat_add_of_lt
    change payload.toNat + 64 < 2 ^ 64
    omega
  have last : (payload + (72#64)).toNat = payload.toNat + 72 := by
    apply BitVec.toNat_add_of_lt
    change payload.toNat + 72 < 2 ^ 64
    omega
  have pointerFrame := htrU64At_call_normal_memory state post arguments p out (payload + (64#64))
    args code aligned fits (Or.inl (by rw [first]; omega)) budget run
  have lengthFrame := htrU64At_call_normal_memory state post arguments p out (payload + (72#64))
    args code aligned fits (Or.inl (by rw [last]; exact before)) budget run
  have metadata := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "htr_u64_at") arguments)
  rw [run] at metadata
  exact entry.after_frame state post payload (4#64) pointer length metadata.2.1 pointerFrame
    (by simpa only [BitVec.add_assoc,show (4#64) * (16#64) + (8#64) = (72#64) by decide] using lengthFrame)

#print axioms htrU64At_call_preserves_payload_requests
end InitECandidate.Runtime
