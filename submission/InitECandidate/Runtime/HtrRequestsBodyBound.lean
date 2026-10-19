import InitECandidate.Runtime.HtrRequestsSuffixBound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.HeapMarkDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure HtrRequestsWorkspace {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap : BitVec 64) : Prop where
  atSha : state.globals.lookup (ofString "sha_st") = some (.val (.word sha))
  atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator))
  atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes))
  atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk))
  atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))
  heapAligned : heap.toNat % 8 = 0
  heapFits : heap.toNat ≤ 33806089496
  recordHeap : record.toNat + 72 < heap.toNat
  accelAligned : accelerator.toNat % 8 = 0
  chunkAligned : chunk.toNat % 8 = 0
  shaRecord : sha.toNat + 64 ≤ record.toNat
  accelRecord : accelerator.toNat + 96 ≤ record.toNat
  chunkRecord : chunk.toNat + 32 ≤ record.toNat
  code : state.code = originalRuntimeCode

theorem HtrRequestsWorkspace.transfer {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {sha accelerator zeroHashes chunk record heap : BitVec 64}
    (ctx : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (globals : post.globals = state.globals) (code : post.code = state.code) :
    HtrRequestsWorkspace post sha accelerator zeroHashes chunk record heap :=
  ⟨(by rw [globals]; exact ctx.atSha),(by rw [globals]; exact ctx.atAccel),(by rw [globals]; exact ctx.atZero),
    (by rw [globals]; exact ctx.atChunk),(by rw [globals]; exact ctx.atHeap),ctx.heapAligned,ctx.heapFits,ctx.recordHeap,
    ctx.accelAligned,ctx.chunkAligned,ctx.shaRecord,ctx.accelRecord,ctx.chunkRecord,code.trans ctx.code⟩

structure HtrRequestsEntryContext {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap out : BitVec 64) : Prop
    extends HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap where
  atRecord : state.locals.lookup (ofString "rq") = some (.val (.word record))
  atOut : state.locals.lookup (ofString "out") = some (.val (.word out))
  decoded : HtrRequestsDecoded state record

theorem HtrRequestsEntryContext.after_frame {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {sha accelerator zeroHashes chunk record heap out : BitVec 64}
    (ctx : HtrRequestsEntryContext state sha accelerator zeroHashes chunk record heap out)
    (locals : ∀ key, key ≠ ofString "mark" → post.locals.lookup key = state.locals.lookup key)
    (globals : post.globals = state.globals) (memory : post.memory = state.memory)
    (domain : post.memaddrs = state.memaddrs) (code : post.code = state.code) :
    HtrRequestsEntryContext post sha accelerator zeroHashes chunk record heap out := by
  have decoded : HtrRequestsDecoded post record := by
    intro index inside
    obtain ⟨p,n,entry,small⟩ := ctx.decoded index inside
    exact ⟨p,n,entry.after_frame state post record index p n domain (congrFun memory _) (congrFun memory _),small⟩
  exact ⟨ctx.toHtrRequestsWorkspace.transfer globals code,(locals _ (by decide)).trans ctx.atRecord,
    (locals _ (by decide)).trans ctx.atOut,decoded⟩

def htrRequestsAllocationCost : Nat := 2 + htrRequestsCost2
def htrRequestsBodyCost : Nat := 1 + htrRequestsAllocationCost

theorem runBounded_htrRequests_allocation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap out : BitVec 64)
    (ctx : HtrRequestsEntryContext state sha accelerator zeroHashes chunk record heap out)
    (budget : htrRequestsAllocationCost ≤ state.clock) :
    RunBounded state (htrRequestsAt 1) htrRequestsAllocationCost := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.panop .mul [.const 5,.const 32]] = some [.val (.word (160#64))] := rfl
  have reached := evaluate_allocation_declaration_reaches state (.panop .mul [.const 5,.const 32]) (ofString "ch") heap (160#64)
    (htrRequestsAt 2) args ctx.code ctx.atHeap ctx.heapFits (by change 2 + htrRequestsCost2 ≤ state.clock at budget; omega)
  rw [← source_htrRequests_alloc] at reached
  exact evaluate_reaches_terminal_bounded state (htrRequestsAt 1) (htrRequestsAt 2) _ 2 _ budget reached (by
    intro next facts remaining
    obtain ⟨locals,memory,installed,domain,globals,cap,covers,aligned⟩ := facts
    have keep (key : MlS) (different : key ≠ ofString "ch") : next.locals.lookup key = state.locals.lookup key := by
      rw [locals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") : next.globals.lookup key = state.globals.lookup key := by
      rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have extent : heap.toNat + 160 ≤ (allocationEnd heap (160#64)).toNat := covers
    have layout : ListHashMemoryLayout next sha accelerator zeroHashes chunk (allocationEnd heap (160#64)) heap record :=
      ⟨⟨(nonHeap _ (by decide)).trans ctx.atSha,(nonHeap _ (by decide)).trans ctx.atAccel,
        (nonHeap _ (by decide)).trans ctx.atZero,
        (by rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]),
        ctx.heapAligned,(by omega),Or.inl (by have := ctx.recordHeap; omega),aligned,cap,
        (by have := ctx.recordHeap; omega),ctx.accelAligned,(by have := ctx.accelRecord; have := ctx.recordHeap; omega),
        (by have := ctx.shaRecord; have := ctx.recordHeap; omega),Or.inr ctx.accelRecord,Or.inr ctx.shaRecord,
        installed.trans ctx.code⟩,(nonHeap _ (by decide)).trans ctx.atChunk,ctx.chunkAligned,
        (by have := ctx.chunkRecord; have := ctx.recordHeap; omega),Or.inr ctx.chunkRecord⟩
    have decoded : HtrRequestsDecoded next record := by
      intro index inside
      obtain ⟨p,n,entry,small⟩ := ctx.decoded index inside
      exact ⟨p,n,entry.after_frame state next record index p n domain (congrFun memory _) (congrFun memory _),small⟩
    exact htrRequests_list0_bound next sha accelerator zeroHashes chunk record heap (allocationEnd heap (160#64)) out
      ⟨layout,(keep _ (by decide)).trans ctx.atRecord,(by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]),
        (keep _ (by decide)).trans ctx.atOut,decoded,(by omega),(by have := ctx.recordHeap; omega),ctx.recordHeap,
        ctx.shaRecord,ctx.accelRecord,ctx.chunkRecord⟩ remaining)

theorem runBounded_htrRequests_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap out : BitVec 64)
    (ctx : HtrRequestsEntryContext state sha accelerator zeroHashes chunk record heap out)
    (budget : htrRequestsBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_requests) htrRequestsBodyCost := by
  rw [sourceFunctionBody_eq_structural]
  change RunBounded state (htrRequestsAt 0) htrRequestsBodyCost
  have reached := evaluate_heapMark_declaration_reaches state (ofString "mark") heap (htrRequestsAt 1) ctx.code ctx.atHeap
    (by change 1 + htrRequestsAllocationCost ≤ state.clock at budget; omega)
  rw [← source_htrRequests_mark] at reached
  exact evaluate_reaches_terminal_bounded state (htrRequestsAt 0) (htrRequestsAt 1) _ 1 _ budget reached (by
    intro next facts remaining
    obtain ⟨locals,memory,globals,installed,domain⟩ := facts
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      rw [locals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    exact runBounded_htrRequests_allocation next sha accelerator zeroHashes chunk record heap out
      (ctx.after_frame keep globals memory domain installed) remaining)

#print axioms HtrRequestsWorkspace.transfer
#print axioms HtrRequestsEntryContext.after_frame
#print axioms runBounded_htrRequests_allocation
#print axioms runBounded_htrRequests_body
end InitECandidate.Runtime
