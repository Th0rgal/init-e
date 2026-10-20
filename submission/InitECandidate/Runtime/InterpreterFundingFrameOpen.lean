import InitECandidate.Runtime.FrameOpenWholeReturnedFunding
import InitECandidate.Runtime.InterpreterFundingLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Real frame_open prepends a physically disjoint funded frame while keeping
all ancestor funding. Pending-child funding is paid explicitly at entry. -/
theorem interpreter_funding_frame_open_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (scratch frame parent previous kind message codePointer codeLength accessAddresses accessSlots empty gas stateGas : BitVec 64)
 (upper : Nat) (ancestors : List InterpreterFundingFrame) (value : ValueHOL 64)
 (layout : InterpreterFundingLayout s scratch.toNat upper ancestors)
 (space : scratch.toNat≤upper) (pendingBudget : interpreterFundingPotential ancestors+gas.toNat≤200000000)
 (atParent : s.globals.lookup (ofString "ev")=some (.val (.word parent)))
 (atPrevious : s.globals.lookup (ofString "cur_cont")=some (.val (.word previous)))
 (atKind : s.locals.lookup (ofString "kind")=some (.val (.word kind)))
 (atMessage : s.locals.lookup (ofString "msg")=some (.val (.word message)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (atEmpty : s.globals.lookup (ofString "evm_empty")=some (.val (.word empty)))
 (frameLower : 280≤frame.toNat) (ordered : frame.toNat≤scratch.toNat) (scratchCap : scratch.toNat≤33806089496)
 (beforeMessage : scratch.toNat≤message.toNat) (messageBound : message.toNat+176≤2^64)
 (messageDomain : ∀offset∈([112,120,152,160] : List (BitVec 64)),s.memaddrs (message+offset))
 (codeAt : s.memory (message+112)=.word codePointer) (lengthAt : s.memory (message+120)=.word codeLength)
 (addressesAt : s.memory (message+152)=.word accessAddresses) (slotsAt : s.memory (message+160)=.word accessSlots)
 (gasAt : s.memory (message+40)=.word gas) (stateGasAt : s.memory (message+48)=.word stateGas)
 (lengthBound : codeLength.toNat≤134217712) (sourceCode : s.code=originalRuntimeCode)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (run : evaluateHOLFiniteState s (frameOpenAt 0)=(some (.returned value),post)) :
 ∃frontier : BitVec 64,let child:=scratchAllocationEnd scratch 280;let record:=scratchAllocationEnd frontier 104
 value=.val (.word child) ∧
 InterpreterFundingLayout post record.toNat upper ({address:=child,gas:=childFunding gas,stateGas:=stateGas}::ancestors) ∧
 interpreterFundingUsed ({address:=child,gas:=childFunding gas,stateGas:=stateGas}::ancestors)=interpreterFundingUsed ancestors ∧
 post.globals.lookup (ofString "ev")=some (.val (.word child)) ∧post.globals.lookup (ofString "cur_cont")=some (.val (.word record)) ∧
 post.globals.lookup (ofString "scratch_ptr")=some (.val (.word record)) ∧post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word (allocationEnd frame 1024))) ∧
 post.memory (child+208)=.word scratch ∧post.memory (child+224)=.word frame ∧
 post.memory record=.word parent ∧post.memory (record+8)=.word previous ∧post.memory (record+16)=.word kind ∧post.memory (record+32)=.word 0 := by
 obtain ⟨frontier,returned,funding,stateGasAtPost,savedScratch,savedFrame,globals,lower,recordExtent,frontierBelow,childExtent,linkParent,linkPrevious,linkKind,done,_,memory,domain,_,_⟩:=frame_open_whole_returned_funding s post scratch frame parent previous kind message codePointer codeLength accessAddresses accessSlots empty gas stateGas value atParent atPrevious atKind atMessage atScratch atFrame atEmpty frameLower ordered scratchCap beforeMessage messageBound messageDomain codeAt lengthAt addressesAt slotsAt gasAt stateGasAt lengthBound sourceCode fullDomain run
 let child:=scratchAllocationEnd scratch 280
 let record:=scratchAllocationEnd frontier 104
 let fresh : InterpreterFundingFrame:={address:=child,gas:=childFunding gas,stateGas:=stateGas}
 have childExtentNat : child.toNat+280≤scratch.toNat:=childExtent
 have recordExtentNat : record.toNat+104≤frontier.toNat:=recordExtent
 have frontierBelowNat : frontier.toNat≤child.toNat:=frontierBelow
 have recordBelow : record.toNat≤scratch.toNat:=by omega
 have freshAt : InterpreterFundingFrameAt post record.toNat upper fresh := by
  constructor
  · dsimp [fresh];omega
  · exact childExtentNat.trans space
  · exact scratchAllocationEnd_mask_aligned scratch 280
  · intro offset member
    rw [domain]
    apply fullDomain
    have small : offset.toNat<280:=by simp [interpreterFundingOffsets] at member;rcases member with rfl|rfl|rfl|rfl <;>decide
    change (child+offset).toNat<33806089496
    rw [BitVec.toNat_add_of_lt (by omega)]
    omega
  · exact funding
  · exact stateGasAtPost
 have olderAt (older : InterpreterFundingFrame) (present : older∈ancestors) : InterpreterFundingFrameAt post record.toNat upper older := by
  have old:=layout.records older present
  have framed : InterpreterFundingFrameAt post scratch.toNat upper older := by
   apply old.after_frame domain
   intro offset member
   apply memory
   have small : offset.toNat<280:=by simp [interpreterFundingOffsets] at member;rcases member with rfl|rfl|rfl|rfl <;>decide
   rw [interpreter_funding_offset_natural older upper old.extent layout.upperBound offset small]
   have:=old.lowerBound
   omega
  exact ⟨recordBelow.trans framed.lowerBound,framed.extent,framed.aligned,framed.readable,framed.funding,framed.stateGasAt⟩
 have newLayout : InterpreterFundingLayout post record.toNat upper (fresh::ancestors) := by
  constructor
  · exact layout.upperBound
  · intro item member
    rcases List.mem_cons.mp member with rfl|older
    · exact freshAt
    · exact olderAt item older
  · apply List.pairwise_cons.mpr
    refine ⟨?_,layout.disjoint⟩
    intro older present
    have old:=layout.records older present
    exact Or.inl (childExtentNat.trans old.lowerBound)
  · change gas.toNat+0+0+interpreterFundingPotential ancestors≤200000000
    omega
 refine ⟨frontier,returned,newLayout,?_,?_,?_,?_,?_,savedScratch,savedFrame,linkParent,linkPrevious,linkKind,done⟩
 · simp [interpreterFundingUsed,childFunding]
 · simp (config:={decide:=true}) [globals,HolFiniteMapExact.lookup_update,FUPDATE,child]
 · simp [globals,HolFiniteMapExact.lookup_update,FUPDATE,record]
 · simp (config:={decide:=true}) [globals,HolFiniteMapExact.lookup_update,FUPDATE,record]
 · simp (config:={decide:=true}) [globals,HolFiniteMapExact.lookup_update,FUPDATE]
#print axioms interpreter_funding_frame_open_returned
end InitECandidate.Runtime
