import InitECandidate.Runtime.HtrPayloadTxAllocationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The original allocation and declaration reach the checked loop invariant,
including allocator-derived geometry, or abort within the allocation budget. -/
theorem htrPayload_tx_allocation_frame_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk array heap input inputLength count : BitVec 64)
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (chunkGlobal : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (countLocal : state.locals.lookup (ofString "ntx") = some (.val (.word count)))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (small : count.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : 2 ≤ state.clock) :
    Reaches state (htrPayloadAt 19)
      (fun next => HtrPayloadTxState pointer accelerator zeroHashes chunk array heap
          (allocationEnd heap (htrPayloadTxAllocationSize count)) input inputLength count next count.toNat ∧
        next.code = originalRuntimeCode ∧
        heap.toNat + count.toNat * 32 ≤ 33806089496 ∧
        (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat % 8 = 0 ∧
        (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat ≤ 33806089496 ∧
        next.memory = state.memory ∧ next.memaddrs = state.memaddrs ∧
        next.globals = (setGlobalHOLFinite (ofString "heap_ptr")
          (.val (.word (allocationEnd heap (htrPayloadTxAllocationSize count)))) state).globals ∧
        (∀ key, key ≠ ofString "roots" → key ≠ ofString "i" → next.locals.lookup key = state.locals.lookup key) ∧
        heap.toNat + count.toNat * 32 + 32 ≤ (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat)
      2 (htrPayloadAt 21) := by
  have allocated := evaluate_allocation_declaration_reaches state
    (.op .add [.panop .mul [.var .local (ofString "ntx"),.const 32],.const 32])
    (ofString "roots") heap (htrPayloadTxAllocationSize count) (htrPayloadAt 20)
    (htrPayload_tx_allocation_arguments state count countLocal) code heapGlobal heapBound budget
  rw [← source_htrPayload_tx_allocation] at allocated
  exact reaches_trans state (htrPayloadAt 19) (htrPayloadAt 20) (htrPayloadAt 21)
    (AllocationDeclarationReady state (ofString "roots") heap (htrPayloadTxAllocationSize count))
    _ 2 0 allocated (by
      intro ready allocation
      have initialized := htrPayload_tx_initialize state ready pointer accelerator zeroHashes chunk array heap
        input inputLength count pointerGlobal accelGlobal zeroGlobal chunkGlobal arrayLocal countLocal slices allocation
      rw [source_htrPayload_tx_zero]
      apply reaches_dec
      intro value evaluated
      have reduced : some (.val (.word (0#64))) = some value := evaluated
      have equal := (Option.some.inj reduced).symm
      subst value
      have geometry := htrPayload_tx_allocation_geometry state ready heap count small allocation
      refine ⟨0#64,rfl,initialized,allocation.2.2.1.trans code,geometry.2.1,geometry.2.2.1,geometry.2.2.2,
        allocation.2.1,allocation.2.2.2.1,allocation.2.2.2.2.1,?_,geometry.1⟩
      intro key notRoots notCounter
      change (ready.locals.update _).lookup key = _
      rw [allocation.1]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notRoots,Ne.symm notCounter])


#print axioms htrPayload_tx_allocation_frame_reaches
end InitECandidate.Runtime
