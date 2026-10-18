import InitECandidate.Runtime.SszSplitVarListDeclarationReturned
import InitECandidate.Runtime.PayloadSplitSuffixBound
import InitECandidate.Runtime.PayloadTransactionSuffixMemoryFrame
import InitECandidate.Runtime.DecodeBytesListBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Globals equal except possibly heap_ptr. -/
def GlobalsExceptHeap {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ k, k ≠ ofString "heap_ptr" → t.globals.lookup k = s.globals.lookup k

/-- A word strictly below the split array's base is outside every slice cell. -/
theorem sszSlices_frame_below {F : Type} (entry : PanSemStateFiniteExact 64 F) (pointer length heapPointer w : BitVec 64)
    (bodyPost : PanSemStateFiniteExact 64 F)
    (slices : SszSplitVarListSlicesReturned entry pointer length heapPointer bodyPost)
    (heapBound : heapPointer.toNat ≤ 33806089496) (below : w.toNat < heapPointer.toNat) :
    bodyPost.memory w = entry.memory w := by
  rcases slices with ⟨_, mem⟩ | ⟨first, _, small, off, _, frame⟩
  · rw [mem]
  · apply frame w
    intro k hk
    have cnt : (first >>> (2 : Nat)).toNat = first.toNat / 4 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [cnt] at hk
    have k16 : (k * 16).toNat = k.toNat * 16 := by rw [BitVec.toNat_mul]; simp; omega
    have c0 : (heapPointer + k * 16).toNat = heapPointer.toNat + k.toNat * 16 := by
      rw [BitVec.toNat_add, k16]; simp; omega
    have c8 : (heapPointer + k * 16 + 8).toNat = heapPointer.toNat + k.toNat * 16 + 8 := by
      rw [BitVec.toNat_add, c0]; simp; omega
    constructor
    · intro e; have := congrArg BitVec.toNat e; omega
    · intro e; have := congrArg BitVec.toNat e; omega

/-- The returned split declaration and transaction suffix keep a watched word
below the entry heap pointer and all globals other than heap_ptr. -/
theorem payload_split_header_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload pointer txs withdrawals balance heapPointer w : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atTxs : state.locals.lookup (ofString "o_txs") = some (.val (.word txs)))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496)
    (header32 : state.memaddrs (payload + 32)) (header40 : state.memaddrs (payload + 40))
    (separate : ∀ offset : BitVec 64, offset ∈ ([32,40,48,56,64,72,80,88,96,104,112,120,128] : List (BitVec 64)) →
      w ≠ payload + offset)
    (below : w.toNat < heapPointer.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 16) = (some (.returned value),post)) :
    post.memory w = state.memory w ∧ GlobalsExceptHeap state post := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      payloadSplitArguments = some [.val (.word (pointer + txs)),.val (.word (withdrawals - txs)),
        .val (.word (9223372036854775807 : BitVec 64))] := by
    simp [payloadSplitArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atTxs,atWithdrawals,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_payload_split_call] at run
  obtain ⟨v, bodyPost, output, bodyRun, ret, slices, tail, pm, pg, pd⟩ :=
    sszSplitVarList_declaration_returned state post (ofString "txs") (payloadAt 17) payloadSplitArguments
      (pointer + txs) (withdrawals - txs) 9223372036854775807 heapPointer value args code heap heapBound run
  obtain ⟨arr, count, hv, _, _⟩ := sszSplitReturned_count _ _ _ _ _ v ret
  have metadata := evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite state (sszSplitCalleeLocals (pointer + txs) (withdrawals - txs) 9223372036854775807))
    (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
  rw [bodyRun] at metadata
  dsimp only at metadata
  subst hv
  generalize hr : setVarHOLFinite (ofString "txs") (.rStruct [.val (.word arr), .val (.word count)])
    ({bodyPost with locals := state.locals} : PanSemStateFiniteExact 64 F) = ready at tail
  have lk : ∀ k, k ≠ ofString "txs" → ready.locals.lookup k = state.locals.lookup k := by
    intro k hk; rw [← hr]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  obtain ⟨frame, tailGlobals⟩ := payload_transaction_suffix_memory_frame ready output payload arr count withdrawals
    balance w value ((lk _ (by decide)).trans atPayload)
    (by rw [← hr]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    ((lk _ (by decide)).trans atWithdrawals) ((lk _ (by decide)).trans atBalance)
    (by rw [← hr]; exact metadata.2.1 ▸ header32) (by rw [← hr]; exact metadata.2.1 ▸ header40) separate
    (by rw [← hr]; exact metadata.1.trans code) tail
  have below' := sszSlices_frame_below _ _ _ heapPointer w bodyPost slices heapBound below
  refine ⟨?_, ?_⟩
  · rw [pm, frame, ← hr]; exact below'
  · intro k hk
    rw [pg, tailGlobals, ← hr]
    show bodyPost.globals.lookup k = state.globals.lookup k
    rcases ret with ⟨_, _, g⟩ | ⟨_, first, _, _, _, _, _, g⟩
    · rw [g]; rfl
    · rw [g]; simp [setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]; rfl

#print axioms payload_split_header_frame
end InitECandidate.Runtime
