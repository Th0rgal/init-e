import InitECandidate.Runtime.HtrRequestsSource
import InitECandidate.Runtime.HtrRequestListUniformBound
import InitECandidate.Runtime.HtrRequestListGlobals
import InitECandidate.Runtime.HtrPcontainerCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The five request pointer/count pairs, with counts bounded by the input arena. -/
def HtrRequestsDecoded {F : Type} (state : PanSemStateFiniteExact 64 F) (record : BitVec 64) : Prop :=
  ∀ index : BitVec 64, index.toNat ≤ 4 → ∃ pointer count : BitVec 64,
    RlpSliceEntry state record index pointer count ∧ count.toNat ≤ 134217712

structure HtrRequestsContext {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record chunks heap out : BitVec 64) : Prop where
  layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap chunks record
  atRecord : state.locals.lookup (ofString "rq") = some (.val (.word record))
  atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks))
  atOut : state.locals.lookup (ofString "out") = some (.val (.word out))
  decoded : HtrRequestsDecoded state record
  chunksFits : chunks.toNat + 160 ≤ 33806089496
  recordHeap : record.toNat + 72 < heap.toNat
  recordChunks : record.toNat + 72 < chunks.toNat
  shaRecord : sha.toNat + 64 ≤ record.toNat
  accelRecord : accelerator.toNat + 96 ≤ record.toNat
  chunkRecord : chunk.toNat + 32 ≤ record.toNat

theorem HtrRequestsContext.after_call {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {sha accelerator zeroHashes chunk record chunks heap out : BitVec 64}
    (ctx : HtrRequestsContext state sha accelerator zeroHashes chunk record chunks heap out)
    (locals : ∀ key, post.locals.lookup key = state.locals.lookup key)
    (globals : post.globals = state.globals) (code : post.code = state.code)
    (decoded : HtrRequestsDecoded post record) :
    HtrRequestsContext post sha accelerator zeroHashes chunk record chunks heap out :=
  ⟨ctx.layout.transfer globals code,(locals _).trans ctx.atRecord,(locals _).trans ctx.atChunks,
    (locals _).trans ctx.atOut,decoded,ctx.chunksFits,ctx.recordHeap,ctx.recordChunks,ctx.shaRecord,ctx.accelRecord,ctx.chunkRecord⟩

def HtrRequestsSuffixBound (index cost : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (sha accelerator zeroHashes chunk record chunks heap out : BitVec 64),
    HtrRequestsContext state sha accelerator zeroHashes chunk record chunks heap out → cost ≤ state.clock →
    RunBounded state (htrRequestsAt index) cost

def htrRequestsCost7 : Nat := htrPcontainerBodyCost + 2

theorem htrRequests_hash_bound : HtrRequestsSuffixBound 7 htrRequestsCost7 := by
  intro F state sha accelerator zeroHashes chunk record chunks heap out ctx budget
  let arguments : List (ExpHOL 64) := [.var .local (ofString "ch"),.const 5,.var .local (ofString "out")]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word chunks),.val (.word (5#64)),.val (.word out)] := by
    simp [arguments,evalListHOLExact,evalHOLExact,ctx.atChunks,ctx.atOut]
  have first := runBounded_htrPcontainer_call state none arguments chunks (5#64) out heap args (by decide) ctx.layout.atHeap
    ctx.layout.heapFits ctx.layout.code (by change htrPcontainerBodyCost + 2 ≤ state.clock at budget; omega)
  rw [source_htrRequests_hash]
  exact RunBounded.seq (tail := .seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) (.return (.const 0)))
    (b := 1) first budget (by
      intro post normal postCode remaining
      exact RunBounded.ofProg
        (ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))
        (postCode.trans ctx.layout.code) remaining)

theorem htrRequests_list_step (index next cost : Nat) (tag size offset : BitVec 64)
    (tagBound : tag.toNat ≤ 4) (offsetBound : offset.toNat ≤ 128) (offsetAligned : offset.toNat % 8 = 0)
    (source : htrRequestsAt index = .seq (.call (some (none,none)) (ofString "htr_request_list")
      (htrRequestsListArguments tag size offset)) (htrRequestsAt next))
    (tail : HtrRequestsSuffixBound next cost) :
    HtrRequestsSuffixBound index ((htrRequestListUniformCost + 1) + cost) := by
  intro F state sha accelerator zeroHashes chunk record chunks heap out ctx budget
  obtain ⟨pointer,count,entry,small⟩ := ctx.decoded tag tagBound
  let arguments := htrRequestsListArguments tag size offset
  have args := htrRequests_list_arguments state record tag pointer count chunks size offset ctx.atRecord ctx.atChunks entry
  have firstBudget : htrRequestListUniformCost + 1 ≤ state.clock := (Nat.le_add_right _ _).trans budget
  have first := runBounded_htrRequestList_call_uniform state none arguments tag pointer count size (chunks + offset) heap args
    ctx.layout.atHeap small ctx.layout.heapFits ctx.layout.code firstBudget
  have natural : (chunks + offset).toNat = chunks.toNat + offset.toNat := by
    apply BitVec.toNat_add_of_lt
    have := ctx.chunksFits
    omega
  have aligned : (chunks + offset).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,ctx.layout.outAligned,offsetAligned]
  have layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap (chunks + offset) record :=
    ⟨⟨ctx.layout.atSha,ctx.layout.atAccel,ctx.layout.atZero,ctx.layout.atHeap,aligned,
      (by rw [natural]; have := ctx.chunksFits; omega),Or.inl (by rw [natural]; have := ctx.recordChunks; omega),
      ctx.layout.heapAligned,ctx.layout.heapFits,ctx.layout.heapBefore,ctx.layout.accelAligned,ctx.layout.accelFits,
      ctx.layout.shaFits,ctx.layout.accelOutside,ctx.layout.shaOutside,ctx.layout.code⟩,
      ctx.layout.atChunk,ctx.layout.chunkAligned,ctx.layout.chunkFits,ctx.layout.chunkOutside⟩
  rw [source]
  exact RunBounded.seq first budget (by
    intro post normal postCode remaining
    change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_request_list") arguments) = (none,post) at normal
    have globals := htrRequestList_call_normal_globals state post arguments tag pointer count size (chunks + offset) heap args ctx.layout.atHeap
      ctx.layout.code normal
    have keep (key : MlS) : post.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_request_list") arguments) rfl state
        (by rw [normal]; exact Or.inl rfl)
      simpa only [normal] using kept
    have decoded : HtrRequestsDecoded post record := by
      intro field inside
      obtain ⟨p,n,old,bound⟩ := ctx.decoded field inside
      exact ⟨p,n,htrRequestList_call_normal_decoded_frame state post arguments sha accelerator zeroHashes chunk tag pointer count size heap
        (chunks + offset) record field p n layout args old inside ctx.recordHeap (by rw [natural]; have := ctx.recordChunks; omega)
        ctx.shaRecord ctx.accelRecord ctx.chunkRecord small
        ((Nat.add_le_add_right (htrRequestList_cost_le_uniform count small) 1).trans firstBudget) normal,bound⟩
    exact tail post sha accelerator zeroHashes chunk record chunks heap out (ctx.after_call keep globals postCode decoded) remaining)

def htrRequestsCost6 : Nat := (htrRequestListUniformCost + 1) + htrRequestsCost7
def htrRequestsCost5 : Nat := (htrRequestListUniformCost + 1) + htrRequestsCost6
def htrRequestsCost4 : Nat := (htrRequestListUniformCost + 1) + htrRequestsCost5
def htrRequestsCost3 : Nat := (htrRequestListUniformCost + 1) + htrRequestsCost4
def htrRequestsCost2 : Nat := (htrRequestListUniformCost + 1) + htrRequestsCost3

theorem htrRequests_list4_bound : HtrRequestsSuffixBound 6 htrRequestsCost6 :=
  htrRequests_list_step 6 7 _ 4 68 128 (by decide) (by decide) (by decide) source_htrRequests_list_4 htrRequests_hash_bound

theorem htrRequests_list3_bound : HtrRequestsSuffixBound 5 htrRequestsCost5 :=
  htrRequests_list_step 5 6 _ 3 184 96 (by decide) (by decide) (by decide) source_htrRequests_list_3 htrRequests_list4_bound

theorem htrRequests_list2_bound : HtrRequestsSuffixBound 4 htrRequestsCost4 :=
  htrRequests_list_step 4 5 _ 2 116 64 (by decide) (by decide) (by decide) source_htrRequests_list_2 htrRequests_list3_bound

theorem htrRequests_list1_bound : HtrRequestsSuffixBound 3 htrRequestsCost3 :=
  htrRequests_list_step 3 4 _ 1 76 32 (by decide) (by decide) (by decide) source_htrRequests_list_1 htrRequests_list2_bound

theorem htrRequests_list0_bound : HtrRequestsSuffixBound 2 htrRequestsCost2 :=
  htrRequests_list_step 2 3 _ 0 192 0 (by decide) (by decide) (by decide) source_htrRequests_list_0 htrRequests_list1_bound

#print axioms HtrRequestsContext.after_call
#print axioms htrRequests_hash_bound
#print axioms htrRequests_list_step
#print axioms htrRequests_list4_bound
#print axioms htrRequests_list3_bound
#print axioms htrRequests_list2_bound
#print axioms htrRequests_list1_bound
#print axioms htrRequests_list0_bound
end InitECandidate.Runtime
