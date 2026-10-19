import InitECandidate.Runtime.HtrNewPayloadAllocationBound
import InitECandidate.Runtime.HtrNewPayloadPayloadGuarded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem runBounded_htrNewPayload_allocation_guarded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si out payload blobs blobCount parentRoot
      array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength : BitVec 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (decoded : HtrRequestsDecoded state record)
    (header : HtrNewPayloadHeader state si payload blobs blobCount parentRoot record)
    (payloadDecoded : HtrPayloadDecoded state payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (siRecord : si.toNat + 32 < record.toNat) (recordBefore : record.toNat + 72 < heap.toNat)
    (shaSi : sha.toNat + 64 ≤ si.toNat) (accelSi : accelerator.toNat + 96 ≤ si.toNat)
    (chunkSi : chunk.toNat + 32 ≤ si.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (chunkArray : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (accelArray : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (shaArray : count ≠ 0 → sha.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (shaPayload : sha.toNat + 64 ≤ payload.toNat)
    (budget : htrNewPayloadAllocationCost ≤ state.clock) :
    RunBounded state (htrNewPayloadAt 1) htrNewPayloadAllocationCost := by
  change 2 + htrNewPayloadPayloadCost ≤ state.clock at budget
  let argument : ExpHOL 64 := .panop .mul [.const 4,.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word (128#64))] := by
    simp [argument,evalListHOLExact,evalHOLExact,wordOpHOL,wordOp,panOpHOL,isWfShapeExactHOL,valueIsWord,valueWord]
  have reached := evaluate_allocation_declaration_reaches state argument (ofString "ch") heap (128#64) (htrNewPayloadAt 2)
    args workspace.code workspace.atHeap workspace.heapFits (by omega)
  have source : htrNewPayloadAt 1 = .decCall (ofString "ch") .one (ofString "alloc") [argument] (htrNewPayloadAt 2) := rfl
  rw [← source] at reached
  exact evaluate_reaches_terminal_bounded state (htrNewPayloadAt 1) (htrNewPayloadAt 2) _ 2 _ budget reached (by
    intro next facts remaining
    obtain ⟨locals,memory,installed,domain,globals,cap,covers,aligned⟩ := facts
    have keep (key : MlS) (different : key ≠ ofString "ch") : next.locals.lookup key = state.locals.lookup key := by
      rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") : next.globals.lookup key = state.globals.lookup key := by
      rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have coversNat : heap.toNat + 128 ≤ (allocationEnd heap (128#64)).toNat := covers
    have workspaceNext : HtrRequestsWorkspace next sha accelerator zeroHashes chunk record (allocationEnd heap (128#64)) :=
      ⟨(nonHeap _ (by decide)).trans workspace.atSha,(nonHeap _ (by decide)).trans workspace.atAccel,
        (nonHeap _ (by decide)).trans workspace.atZero,(nonHeap _ (by decide)).trans workspace.atChunk,
        (by rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]),aligned,cap,
        (by omega),workspace.accelAligned,workspace.chunkAligned,workspace.shaRecord,workspace.accelRecord,workspace.chunkRecord,
        installed.trans workspace.code⟩
    have decodedNext : HtrRequestsDecoded next record := by
      intro index inside
      obtain ⟨p,n,entry,small⟩ := decoded index inside
      exact ⟨p,n,entry.after_frame state next record index p n domain (congrFun memory _) (congrFun memory _),small⟩
    have headerNext := header.after_frame domain (fun _ _ => congrFun memory _)
    exact runBounded_htrNewPayload_payload_suffix_guarded next sha accelerator zeroHashes chunk record (allocationEnd heap (128#64)) si heap out
      payload blobs blobCount parentRoot array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength
      workspaceNext decodedNext headerNext (payloadDecoded.after_frame domain memory) ((keep _ (by decide)).trans atSi)
      (by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]) ((keep _ (by decide)).trans atOut)
      workspace.heapAligned coversNat siRecord recordBefore shaSi accelSi chunkSi (by omega) chunkArray accelArray shaArray
      (by omega) chunkPayload accelPayload shaPayload remaining)

#print axioms runBounded_htrNewPayload_allocation_guarded
end InitECandidate.Runtime
