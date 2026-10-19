import InitECandidate.Runtime.DecodeBranchPlacement
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Live continuation data. The child index may advance; unlike the decoder
initialization predicate it is not fixed to zero. The hash and occupancy cells
are omitted because normal source evaluation checks their loaded values. -/
def WitnessPhysicalRecord {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record previous input inputLength frontier : BitVec 64) (persistentFloor : Nat) : Prop :=
  0 < record.toNat ∧ record.toNat+88 ≤ persistentFloor ∧
  (∀ offset : Nat, offset < 88 → s.memaddrs (record+BitVec.ofNat 64 offset)) ∧
  s.memory record = .word previous ∧
  ∃ array count stage pointer length : BitVec 64,
    (stage=1 ∧ count=2 ∨ stage=2 ∧ count=17) ∧
    s.memory (record+8)=.word stage ∧ s.memory (record+24)=.word array ∧
    s.memory (record+48)=.word pointer ∧ s.memory (record+56)=.word length ∧
    record.toNat+88 ≤ array.toNat ∧ array.toNat+count.toNat*16 ≤ frontier.toNat ∧
    RlpSliceInputPrefix s array input inputLength count.toNat ∧
    (stage=1 → ∃ nibs nibbles : BitVec 64,
      s.memory (record+64)=.word nibs ∧ s.memory (record+72)=.word nibbles) ∧
    (stage=2 → ∃ branch index : BitVec 64,
      s.memory (record+16)=.word branch ∧ s.memory (record+32)=.word index ∧ index.toNat<16 ∧
      persistentFloor ≤ branch.toNat ∧ array.toNat+272 ≤ branch.toNat ∧
      branch.toNat+176 ≤ frontier.toNat ∧ branch.toNat%8=0)

/-- Actual freshly pushed metadata initializes the live-record invariant.
The caller supplies the real link, fresh-record extent, and final heap word. -/
theorem witness_physical_record_of_pushed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record previous pointer length input inputLength frontier : BitVec 64)
    (ceiling persistentFloor initialHeap : Nat)
    (valid : DecoderPlacedPushedTable s record pointer length input inputLength ceiling initialHeap)
    (positive : 0 < record.toNat) (recordBefore : record.toNat+88 ≤ ceiling)
    (belowFloor : record.toNat+88 ≤ persistentFloor) (heapAbove : persistentFloor ≤ initialHeap)
    (accessible : ∀ offset : Nat, offset<88 → s.memaddrs (record+BitVec.ofNat 64 offset))
    (link : s.memory record=.word previous)
    (heap : s.globals.lookup (Flapjack.Basis.Pure.MlString.ofString "heap_ptr")=some (.val (.word frontier))) :
    WitnessPhysicalRecord s record previous input inputLength frontier persistentFloor := by
  obtain ⟨array,count,stage,finalHeap,kind,fields,table,above,extent,atHeap,capped,aligned⟩ := valid.1
  have sameHeap : finalHeap=frontier := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (atHeap.symm.trans heap)))
  subst finalHeap
  obtain ⟨atStage,atArray,atPointer,atLength,nibs,branch⟩ := fields
  refine ⟨positive,belowFloor,accessible,link,array,count,stage,pointer,length,kind,atStage,atArray,
    atPointer,atLength,by omega,extent,table,nibs,?_⟩
  intro two
  obtain ⟨br,atBranch,atIndex,_⟩ := branch two
  obtain ⟨placedArray,placedBranch,placedHeap,placedArrayCell,placedBranchCell,floorBound,
    tableEnd,branchEnd,branchAligned,placedHeapCell,_⟩ := valid.2 (by rw [atStage,two])
  have sameArray : placedArray=array := HolWordLab.word.inj (placedArrayCell.symm.trans atArray)
  have sameBranch : placedBranch=br := HolWordLab.word.inj (placedBranchCell.symm.trans atBranch)
  have samePlacedHeap : placedHeap=frontier := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (placedHeapCell.symm.trans heap)))
  subst placedArray; subst placedBranch; subst placedHeap
  exact ⟨br,0,atBranch,atIndex,by decide,heapAbove.trans floorBound,tableEnd,branchEnd,branchAligned⟩

#print axioms witness_physical_record_of_pushed
end InitECandidate.Runtime
