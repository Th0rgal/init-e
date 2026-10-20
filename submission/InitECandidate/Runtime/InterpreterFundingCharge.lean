import InitECandidate.Runtime.InterpreterFundingLayout
import InitECandidate.Runtime.OriginalChargeGasCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def InterpreterFundingFrame.charged (frame : InterpreterFundingFrame) (amount : BitVec 64) : InterpreterFundingFrame :=
 {frame with gas:=frame.gas.charge amount}
/-- Actual charge_gas preserves the physical global funding registry, all older
frame words, and input memory above its arena, while increasing global used gas. -/
theorem interpreter_funding_charge_call (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (lower upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s lower upper (current::ancestors))
 (amount : BitVec 64) (argument : ExpHOL 64)
 (code : s.code=originalRuntimeCode)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word amount)])
 (enough : amount≤current.gas.left) (ticks : s.clock≠0) :
 ∃post,evaluateHOLFiniteState s (.call (some (none,none)) (ofString "charge_gas") [argument])=(none,post) ∧
 InterpreterFundingLayout post lower upper (current.charged amount::ancestors) ∧
 interpreterFundingUsed (current.charged amount::ancestors)=interpreterFundingUsed (current::ancestors)+amount.toNat ∧
 post.globals=s.globals ∧post.clock=s.clock-1 ∧
 (∀watched : BitVec 64,upper≤watched.toNat→post.memory watched=s.memory watched) := by
 have currentAt:=layout.records current (by simp)
 have currentBudget : current.gas.potential≤200000000 := by
  have budget:=layout.budget
  change current.gas.potential+interpreterFundingPotential ancestors≤200000000 at budget
  omega
 let post:=chargeGasCallPost s current.address current.gas amount
 have run:=evaluate_chargeGas_call s argument current.address amount current.gas args
  (by rw [code];exact originalRuntimeCode_chargeGas_lookup) ticks atCurrent
  (currentAt.readable 64 (by simp [interpreterFundingOffsets]))
  (currentAt.readable 184 (by simp [interpreterFundingOffsets])) currentAt.funding enough
 have chargedAt : InterpreterFundingFrameAt post lower upper (current.charged amount) := by
  constructor
  · exact currentAt.lowerBound
  · exact currentAt.extent
  · exact currentAt.aligned
  · exact currentAt.readable
  · exact chargeGasCallPost_funding s current.address amount current.gas currentAt.funding
  · simpa [post,chargeGasCallPost,sourceWriteWord,InterpreterFundingFrame.charged] using currentAt.stateGasAt
 have olderAt (older : InterpreterFundingFrame) (present : older∈ancestors) :
  InterpreterFundingFrameAt post lower upper older := by
  have valid:=layout.records older (by simp [present])
  have separate : interpreterFundingDisjoint current older := (List.pairwise_cons.mp layout.disjoint).1 older present
  apply valid.after_frame (post:=post) rfl
  intro offset member
  have small : offset.toNat<280 := by
   simp [interpreterFundingOffsets] at member
   rcases member with rfl|rfl|rfl|rfl <;>decide
  have notLeft:=interpreter_funding_offsets_distinct current older upper currentAt.extent valid.extent layout.upperBound separate 64 offset (by decide) small
  have notUsed:=interpreter_funding_offsets_distinct current older upper currentAt.extent valid.extent layout.upperBound separate 184 offset (by decide) small
  have leftNe : older.address+offset≠current.address+64#64 := Ne.symm notLeft
  have usedNe : older.address+offset≠current.address+184#64 := Ne.symm notUsed
  simp [post,chargeGasCallPost,sourceWriteWord,leftNe,usedNe]
 refine ⟨post,run,?_,?_,rfl,rfl,?_⟩
 · constructor
   · exact layout.upperBound
   · intro record present
     rcases List.mem_cons.mp present with rfl|older
     · exact chargedAt
     · exact olderAt record older
   · apply List.pairwise_cons.mpr
     constructor
     · intro older present
       exact (List.pairwise_cons.mp layout.disjoint).1 older present
     · exact (List.pairwise_cons.mp layout.disjoint).2
   · change (current.gas.charge amount).potential+interpreterFundingPotential ancestors≤200000000
     rw [current.gas.charge_potential amount currentBudget enough]
     exact layout.budget
 · have growth:=current.gas.charge_used_growth amount currentBudget enough
   change (current.gas.charge amount).used.toNat+interpreterFundingUsed ancestors=
    current.gas.used.toNat+interpreterFundingUsed ancestors+amount.toNat
   rw [growth];omega
 · intro watched above
   have leftNat:=interpreter_funding_offset_natural current upper currentAt.extent layout.upperBound 64 (by decide)
   have usedNat:=interpreter_funding_offset_natural current upper currentAt.extent layout.upperBound 184 (by decide)
   have notLeft : watched≠current.address+64 := by
    intro same
    have natural:=congrArg BitVec.toNat same
    rw [leftNat] at natural
    change watched.toNat=current.address.toNat+64 at natural
    have extent:=currentAt.extent
    omega
   have notUsed : watched≠current.address+184 := by
    intro same
    have natural:=congrArg BitVec.toNat same
    rw [usedNat] at natural
    change watched.toNat=current.address.toNat+184 at natural
    have extent:=currentAt.extent
    omega
   have leftNe : watched≠current.address+64#64 := notLeft
   have usedNe : watched≠current.address+184#64 := notUsed
   simp [post,chargeGasCallPost,sourceWriteWord,leftNe,usedNe]
#print axioms interpreter_funding_charge_call
end InitECandidate.Runtime
