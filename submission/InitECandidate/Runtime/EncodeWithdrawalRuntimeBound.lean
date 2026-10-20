import InitECandidate.Runtime.EncodeWithdrawalFirstFieldBound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def encodeWithdrawalSourceCost (DF : Nat) := 2+withdrawalFirstFieldsCost DF
/-- Complete actual withdrawal encoder. The initial allocator either supplies
 its real buffer geometry or rejects; all four writers and final list copy
 are bounded from their actual executions, including failed SSZ reads. -/
theorem encode_withdrawal_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (heap : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF+8≤2^62)
 (heapFence : 33806089496≤DF)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapCap : heap.toNat≤33806089496)
 (budget : encodeWithdrawalSourceCost DF≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) (encodeWithdrawalSourceCost DF) := by
 have stage0 : encodeWithdrawalAt 0=.decCall (ofString "buf") .one (ofString "alloc") [.const 64] (encodeWithdrawalAt 1) := rfl
 have reached:=evaluate_allocation_declaration_reaches s (.const 64) (ofString "buf") heap 64 (encodeWithdrawalAt 1)
  (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) code atHeap heapCap
  (by unfold encodeWithdrawalSourceCost at budget;omega)
 rw [←stage0] at reached
 rw [sourceFunctionBody_eq_structural]
 change RunBounded s (encodeWithdrawalAt 0) (encodeWithdrawalSourceCost DF)
 apply evaluate_reaches_terminal_bounded s _ _ _ 2 (withdrawalFirstFieldsCost DF) budget reached
 intro ready allocation remaining
 obtain ⟨locals,memory,installed,domain,globals,nextCap,covers,nextAligned⟩:=allocation
 have buffer : ready.locals.lookup (ofString "buf")=some (.val (.word heap)) := by
  rw [locals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
 have cursorNat : (heap+9#64).toNat=heap.toNat+9 := by
  rw [BitVec.toNat_add]
  apply Nat.mod_eq_of_lt
  change heap.toNat+9<2^64
  omega
 have stage1 : encodeWithdrawalAt 1=.dec (ofString "p") .one
  (.op .add [.var .local (ofString "buf"),.const 9]) (encodeWithdrawalAt 2) := rfl
 rw [stage1]
 apply RunBounded.decWord (body:=encodeWithdrawalAt 2) (cost:=withdrawalFirstFieldsCost DF) ready (ofString "p") _ (heap+9#64)
 · simp [evalHOLExact,evalListHOLExact,buffer,wordOpHOL,wordOp,valueIsWord,valueWord]
 · have valid : WithdrawalCursorInvariant (setVarHOLFinite (ofString "p") (.val (.word (heap+9#64))) ready) heap DF := by
    refine ⟨installed.trans code,?_,?_,heap+9#64,?_,?_,?_⟩
    · change Fence ready.memaddrs DF;rw [domain];exact fence
    · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using buffer
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [cursorNat]
    · rw [cursorNat]
      change heap.toNat+64≤(allocationEnd heap 64).toNat at covers
      omega
   exact encode_withdrawal_first_field_bounded _ heap DF valid cap remaining
#print axioms encode_withdrawal_body_bounded
end InitECandidate.Runtime
