import InitECandidate.Runtime.HtrNewPayloadSource
import InitECandidate.Runtime.HtrRequestsCallBound
import InitECandidate.Runtime.HtrRequestsGlobals
import InitECandidate.Runtime.MerkleizeCallBound
import InitECandidate.Runtime.VmFn_heap_release
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrNewPayloadFinalCost : Nat := (merkleBodyCost + 1) + 1

theorem runBounded_htrNewPayload_final {F : Type} (state : PanSemStateFiniteExact 64 F) (chunks out heap : BitVec 64)
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrNewPayloadFinalCost ≤ state.clock) :
    RunBounded state (htrNewPayloadAt 6) htrNewPayloadFinalCost := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrNewPayloadMerkleArguments =
      some [.val (.word chunks),.val (.word (4#64)),.val (.word (4#64)),.val (.word out)] := by
    simp [htrNewPayloadMerkleArguments,evalListHOLExact,evalHOLExact,atChunks,atOut]
  have enough : merkleBodyCost + 1 ≤ state.clock := (Nat.le_add_right (merkleBodyCost + 1) 1).trans budget
  have first := runBounded_merkleize_call state none htrNewPayloadMerkleArguments chunks 4 4 out heap args (by decide) atHeap heapBound code enough
  rw [source_htrNewPayload_merkle]
  exact RunBounded.seq (b := 1) first budget (by
    intro next normal nextCode remaining
    rw [source_htrNewPayload_finish]
    exact RunBounded.ofProg
      (ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))
      (nextCode.trans code) remaining)

def htrNewPayloadRequestsCost : Nat := (htrRequestsBodyCost + 1) + htrNewPayloadFinalCost

/-- The actual requests-container call and final Merkle/release suffix have
one bound from decoded request counts and the original workspace geometry. -/
theorem runBounded_htrNewPayload_requests_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si chunks out : BitVec 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (decoded : HtrRequestsDecoded state record)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (domain : state.memaddrs (si + (32#64))) (cell : state.memory (si + (32#64)) = .word record)
    (budget : htrNewPayloadRequestsCost ≤ state.clock) :
    RunBounded state (htrNewPayloadAt 5) htrNewPayloadRequestsCost := by
  have args := htrNewPayload_requests_arguments state si chunks record atSi atChunks domain cell
  have enough : htrRequestsBodyCost + 1 ≤ state.clock :=
    (Nat.le_add_right (htrRequestsBodyCost + 1) htrNewPayloadFinalCost).trans budget
  have first := runBounded_htrRequests_call state none htrNewPayloadRequestsArguments sha accelerator zeroHashes chunk record heap
    (chunks + (96#64)) workspace decoded args enough
  rw [source_htrNewPayload_requests]
  exact RunBounded.seq first budget (by
    intro next normal nextCode remaining
    have globals := htrRequests_call_normal_globals state next htrNewPayloadRequestsArguments record (chunks + (96#64)) heap
      args workspace.atHeap workspace.code normal
    have keep (key : MlS) : next.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_requests") htrNewPayloadRequestsArguments)
        rfl state (by rw [normal]; exact Or.inl rfl)
      rw [normal] at kept
      exact kept
    exact runBounded_htrNewPayload_final next chunks out heap ((keep _).trans atChunks) ((keep _).trans atOut)
      (by rw [globals]; exact workspace.atHeap) workspace.heapFits (nextCode.trans workspace.code) remaining)

#print axioms runBounded_htrNewPayload_final
#print axioms runBounded_htrNewPayload_requests_suffix
end InitECandidate.Runtime
