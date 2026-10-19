import InitECandidate.Runtime.HtrPayloadTxLoopBound
import InitECandidate.Runtime.AllocationDeclarationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPayloadTxAllocationSize (count : BitVec 64) : BitVec 64 := count * (32#64) + (32#64)

theorem source_htrPayload_tx_allocation : htrPayloadAt 19 =
    .decCall (ofString "roots") .one (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "ntx"),.const 32],.const 32]]
      (htrPayloadAt 20) := by rfl

theorem source_htrPayload_tx_zero : htrPayloadAt 20 =
    .dec (ofString "i") .one (.const 0) (htrPayloadAt 21) := by rfl

theorem htrPayload_tx_allocation_size (count : BitVec 64) (small : count.toNat ≤ 134217712) :
    (htrPayloadTxAllocationSize count).toNat = count.toNat * 32 + 32 := by
  have mul : (count * (32#64)).toNat = count.toNat * 32 :=
    BitVec.toNat_mul_of_lt (by change count.toNat * 32 < 2 ^ 64; omega)
  unfold htrPayloadTxAllocationSize
  rw [BitVec.toNat_add_of_lt (by rw [mul]; change count.toNat * 32 + 32 < 2 ^ 64; omega),mul]
  rfl

/-- The successful allocator result provides the roots extent and the next aligned heap frontier. -/
theorem htrPayload_tx_allocation_geometry {F : Type} (state ready : PanSemStateFiniteExact 64 F)
    (heap count : BitVec 64) (small : count.toNat ≤ 134217712)
    (allocated : AllocationDeclarationReady state (ofString "roots") heap
      (htrPayloadTxAllocationSize count) ready) :
    heap.toNat + count.toNat * 32 + 32 ≤ (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat ∧
    heap.toNat + count.toNat * 32 ≤ 33806089496 ∧
    (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat % 8 = 0 ∧
    (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat ≤ 33806089496 := by
  have covers := allocated.2.2.2.2.2.2.1
  rw [htrPayload_tx_allocation_size count small] at covers
  exact ⟨by omega,by have bound := allocated.2.2.2.2.2.1; omega,
    allocated.2.2.2.2.2.2.2,allocated.2.2.2.2.2.1⟩

/-- Allocation and the actual counter declaration establish the complete loop invariant. -/
theorem htrPayload_tx_initialize {F : Type} (state ready : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk array heap input inputLength count : BitVec 64)
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (chunkGlobal : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (countLocal : state.locals.lookup (ofString "ntx") = some (.val (.word count)))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (allocated : AllocationDeclarationReady state (ofString "roots") heap
      (htrPayloadTxAllocationSize count) ready) :
    HtrPayloadTxState pointer accelerator zeroHashes chunk array heap
      (allocationEnd heap (htrPayloadTxAllocationSize count)) input inputLength count
      (setVarHOLFinite (ofString "i") (.val (.word (0#64))) ready) count.toNat := by
  have keepGlobal (key : MlS) (different : key ≠ ofString "heap_ptr") :
      ready.globals.lookup key = state.globals.lookup key := by
    rw [allocated.2.2.2.2.1]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have keepLocal (key : MlS) (different : key ≠ ofString "roots") :
      ready.locals.lookup key = state.locals.lookup key := by
    rw [allocated.1]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  refine {
    pointerGlobal := (keepGlobal _ (by decide)).trans pointerGlobal
    accelGlobal := (keepGlobal _ (by decide)).trans accelGlobal
    zeroGlobal := (keepGlobal _ (by decide)).trans zeroGlobal
    chunkGlobal := (keepGlobal _ (by decide)).trans chunkGlobal
    heapGlobal := ?_
    arrayLocal := ?_
    rootsLocal := ?_
    countLocal := ?_
    slices := ?_
    cursor := ?_ }
  · change ready.globals.lookup _ = _
    rw [allocated.2.2.2.2.1]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · change (ready.locals.update _).lookup _ = _
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using (keepLocal _ (by decide)).trans arrayLocal
  · change (ready.locals.update _).lookup _ = _
    rw [allocated.1]
    simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · change (ready.locals.update _).lookup _ = _
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using (keepLocal _ (by decide)).trans countLocal
  · intro slot inside
    obtain ⟨p,n,entry⟩ := slices slot inside
    exact ⟨p,n,entry.after_frame state _ array slot p n input inputLength
      allocated.2.2.2.1 (congrFun allocated.2.1 _) (congrFun allocated.2.1 _)⟩
  · refine ⟨0#64,?_,by simp,by simp⟩
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

theorem htrPayload_tx_counter_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk array roots heap input inputLength count : BitVec 64)
    (initialized : HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count
      (setVarHOLFinite (ofString "i") (.val (.word (0#64))) state) count.toNat) :
    Reaches state (htrPayloadAt 20)
      (fun next => HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count next count.toNat)
      0 (htrPayloadAt 21) := by
  rw [source_htrPayload_tx_zero]
  apply reaches_dec
  intro value evaluated
  have equal : value = .val (.word (0#64)) := by
    have reduced : some (.val (.word (0#64))) = some value := evaluated
    exact (Option.some.inj reduced).symm
  subst value
  exact ⟨0#64,rfl,initialized⟩

#print axioms htrPayload_tx_counter_reaches
#print axioms htrPayload_tx_initialize
#print axioms source_htrPayload_tx_allocation
#print axioms source_htrPayload_tx_zero
#print axioms htrPayload_tx_allocation_size
#print axioms htrPayload_tx_allocation_geometry
end InitECandidate.Runtime
