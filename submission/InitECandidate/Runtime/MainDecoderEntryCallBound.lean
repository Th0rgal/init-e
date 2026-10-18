import InitECandidate.Runtime.MainDecoderEntryFields
import InitECandidate.Runtime.MainStatelessCallBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def canonicalStatelessCallCost : Nat := 201327178

/-- The complete handled decoder call on every state produced by the
canonical prefix has a uniform bound from the challenge input-size limit. -/
theorem main_decoder_entry_stateless_call_bounded {F : Type}
    (state ready : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready) (budget : canonicalStatelessCallCost ≤ ready.clock) :
    let evaluated := evaluateHOLFiniteState ready mainStatelessCall
    ready.clock ≤ evaluated.2.clock + canonicalStatelessCallCost ∧
      evaluated.2.clock ≤ ready.clock ∧ evaluated.1 ≠ some .timeOut := by
  obtain ⟨length,out,zero,heap,inp,output,z32,small,fits,offsets,atHeap,capped,aligned,lower,
    installed,domain,_,_⟩ := valid.fields
  have costLe : statelessInputBound length + 66 ≤ canonicalStatelessCallCost := by
    unfold statelessInputBound sszSplitBound canonicalStatelessCallCost
    omega
  have heapArena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      heap.toNat ≤ address.toNat → address.toNat < 33806089496 → ready.memaddrs address := by
    intro address cellAligned lo hi
    rw [domain]
    exact arena address cellAligned (by omega) hi
  have cells : ∀ offset ∈ ([0,8,16,24] : List (BitVec 64)),
      ready.memaddrs ((2713715344 : BitVec 64) + offset) := by
    intro offset member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals rw [domain]; exact arena _ (by decide) (by decide) (by decide)
  have bounded := evaluate_main_stateless_call_bounded_cells ready 2713731432 length 2713715344 heap out zero
    inp output z32 offsets (installed.trans code) atHeap capped aligned
    (by change 2713715344 + 32 ≤ heap.toNat; omega)
    (by change 2713731432 + length.toNat < 2 ^ 64; exact fits)
    heapArena (cells 0 (by simp)) (cells 8 (by simp)) (cells 16 (by simp)) (cells 24 (by simp)) (by omega)
  exact ⟨by have spent := bounded.1; omega,bounded.2⟩

#print axioms main_decoder_entry_stateless_call_bounded
end InitECandidate.Runtime
