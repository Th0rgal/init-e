import InitECandidate.Runtime.HtrRequestsBodyBound
import InitECandidate.Runtime.DecodeRequestsReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The ten actual decoder stores form five readable pointer/count entries. -/
theorem reqCells_htrRequestsDecoded {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (record p o0 o1 o2 o3 o4 n0 n1 n2 n3 n4 : BitVec 64)
    (bounds : ∀ n ∈ [n0,n1,n2,n3,n4], n.toNat ≤ 134217712)
    (domains : ∀ cell ∈ reqCellValues p o0 o1 o2 o3 o4 n0 n1 n2 n3 n4, state.memaddrs (record + cell.1))
    (memory : post.memory = memWrites state.memory record (reqCellValues p o0 o1 o2 o3 o4 n0 n1 n2 n3 n4))
    (domain : post.memaddrs = state.memaddrs) : HtrRequestsDecoded post record := by
  let cells := reqCellValues p o0 o1 o2 o3 o4 n0 n1 n2 n3 n4
  have nodup : (cells.map Prod.fst).Nodup := reqCellValues_nodup _ _ _ _ _ _ _ _ _ _ _
  have entry (index pointer count : BitVec 64)
      (hp : (index * (16#64),pointer) ∈ cells) (hn : (index * (16#64) + (8#64),count) ∈ cells) :
      RlpSliceEntry post record index pointer count := by
    refine ⟨?_,?_,?_,?_⟩
    · rw [domain]
      exact domains _ hp
    · rw [domain,BitVec.add_assoc]
      exact domains _ hn
    · rw [memory]
      exact memWrites_cell state.memory record cells nodup _ hp
    · rw [memory,BitVec.add_assoc]
      exact memWrites_cell state.memory record cells nodup _ hn
  intro index inside
  have cases' : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 ∨ index.toNat = 3 ∨ index.toNat = 4 := by omega
  rcases cases' with h | h | h | h | h
  · have equal : index = (0#64) := BitVec.eq_of_toNat_eq h
    subst index
    exact ⟨p + o0,n0,entry _ _ _ (by simp [cells,reqCellValues]) (by simp [cells,reqCellValues]),bounds _ (by simp)⟩
  · have equal : index = (1#64) := BitVec.eq_of_toNat_eq h
    subst index
    exact ⟨p + o1,n1,entry _ _ _ (by simp [cells,reqCellValues]) (by simp [cells,reqCellValues]),bounds _ (by simp)⟩
  · have equal : index = (2#64) := BitVec.eq_of_toNat_eq h
    subst index
    exact ⟨p + o2,n2,entry _ _ _ (by simp [cells,reqCellValues]) (by simp [cells,reqCellValues]),bounds _ (by simp)⟩
  · have equal : index = (3#64) := BitVec.eq_of_toNat_eq h
    subst index
    exact ⟨p + o3,n3,entry _ _ _ (by simp [cells,reqCellValues]) (by simp [cells,reqCellValues]),bounds _ (by simp)⟩
  · have equal : index = (4#64) := BitVec.eq_of_toNat_eq h
    subst index
    exact ⟨p + o4,n4,entry _ _ _ (by simp [cells,reqCellValues]) (by simp [cells,reqCellValues]),bounds _ (by simp)⟩

/-- Accepted offsets bound every count by the request input length. -/
theorem reqArrayFacts_htrRequestsDecoded {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (p length record offsets : BitVec 64) (value : ValueHOL 64)
    (small : length.toNat ≤ 134217712)
    (checked : SszCheckOffsetsReturned state offsets (5#64) (20#64) length (.val (.word (0#64))))
    (facts : ReqArrayFacts state p length record offsets value post) : HtrRequestsDecoded post record := by
  have upper (i : BitVec 64) (inside : i.toNat < 5) :
      (memWord state.memory (offsets + i * (8#64))).toNat ≤ length.toNat := by
    have bound := (checked.2.1 i inside).2.2.1
    exact BitVec.le_def.mp (BitVec.not_lt.mp bound)
  have ordered (i j : BitVec 64) (inside : i.toNat < 5)
      (positive : Compiler.Encoders.Asm.holAsmSignedLess (0#64) i = true)
      (prev : i * (8#64) - (8#64) = j * (8#64)) :
      (memWord state.memory (offsets + j * (8#64))).toNat ≤
        (memWord state.memory (offsets + i * (8#64))).toNat := by
    have bound := ((checked.2.1 i inside).2.2.2 positive).2
    have address : offsets + i * (8#64) - (8#64) = offsets + j * (8#64) := by
      calc
        _ = offsets + (i * (8#64) - (8#64)) := by simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
        _ = _ := congrArg (fun x => offsets + x) prev
    rw [address] at bound
    exact BitVec.le_def.mp (BitVec.not_lt.mp bound)
  let o0 := memWord state.memory offsets
  let o1 := memWord state.memory (offsets + (8#64))
  let o2 := memWord state.memory (offsets + (16#64))
  let o3 := memWord state.memory (offsets + (24#64))
  let o4 := memWord state.memory (offsets + (32#64))
  have countBound (a b size : BitVec 64) (order : a.toNat ≤ b.toNat) (hi : b.toNat ≤ length.toNat) :
      ((b - a) / size).toNat ≤ 134217712 := by
    rw [BitVec.toNat_udiv,BitVec.toNat_sub_of_le (BitVec.le_def.mpr order)]
    exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans (hi.trans small))
  have hi1 : o1.toNat ≤ length.toNat := upper (1#64) (by decide)
  have hi2 : o2.toNat ≤ length.toNat := upper (2#64) (by decide)
  have hi3 : o3.toNat ≤ length.toNat := upper (3#64) (by decide)
  have hi4 : o4.toNat ≤ length.toNat := upper (4#64) (by decide)
  have ord1 : o0.toNat ≤ o1.toNat := by
    simpa [o0,o1] using ordered (1#64) (0#64) (by decide) (by decide) (by decide)
  have ord2 : o1.toNat ≤ o2.toNat := ordered (2#64) (1#64) (by decide) (by decide) (by decide)
  have ord3 : o2.toNat ≤ o3.toNat := ordered (3#64) (2#64) (by decide) (by decide) (by decide)
  have ord4 : o3.toNat ≤ o4.toNat := ordered (4#64) (3#64) (by decide) (by decide) (by decide)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,domains,memory,_,domain⟩ := facts
  apply reqCells_htrRequestsDecoded state post record p o0 o1 o2 o3 o4
    ((o1-o0)/192) ((o2-o1)/76) ((o3-o2)/116) ((o4-o3)/184) ((length-o4)/68) _ domains memory domain
  intro n member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact countBound o0 o1 _ ord1 hi1
  · exact countBound o1 o2 _ ord2 hi2
  · exact countBound o2 o3 _ ord3 hi3
  · exact countBound o3 o4 _ ord4 hi4
  · exact countBound o4 length _ hi4 (Nat.le_refl _)

theorem decodeRequestsReturned_htrRequestsDecoded {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (p length record offsets : BitVec 64) (value : ValueHOL 64) (small : length.toNat ≤ 134217712)
    (facts : DecodeRequestsReturned state p length record offsets value post) : HtrRequestsDecoded post record := by
  obtain ⟨_,memory,_,checked,array⟩ := facts
  exact reqArrayFacts_htrRequestsDecoded {state with memory := memory} post p length record offsets value small checked array

/-- The actual original decoder establishes the hash entry/count premises. -/
theorem htrRequestsDecoded_of_decodeRequests_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (p length record offsets : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word record)))
    (heapBound : record.toNat ≤ 33806089496)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (small : length.toNat ≤ 134217712)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_requests) = (some (.returned value),post)) :
    HtrRequestsDecoded post record := by
  have facts := evaluate_decodeRequests_returned state p length record offsets code atInput atLength atHeap heapBound atOffsets value
    (by rw [run])
  rw [run] at facts
  exact decodeRequestsReturned_htrRequestsDecoded state post p length record offsets value small facts

#print axioms reqCells_htrRequestsDecoded
#print axioms reqArrayFacts_htrRequestsDecoded
#print axioms decodeRequestsReturned_htrRequestsDecoded
#print axioms htrRequestsDecoded_of_decodeRequests_returned
end InitECandidate.Runtime
