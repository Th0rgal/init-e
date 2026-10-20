import InitECandidate.Runtime.SourceDomainExpressionTransfer
namespace InitECandidate.Runtime
open Flapjack

/-- A successful word store makes the same memory update in an enlarged domain. -/
theorem mem_store_source_domain_extend (address : BitVec 64) (value : HolWordLab 64)
 (small large : BitVec 64→Prop) [DecidablePred small] [DecidablePred large]
 (subset : ∀a,small a→large a) (memory output : BitVec 64→HolWordLab 64)
 (run : panMemStoreHOL address value small memory=some output) :
 panMemStoreHOL address value large memory=some output := by
 by_cases accessible : small address
 · simpa only [panMemStoreHOL,if_pos accessible,if_pos (subset address accessible)] using run
 · simp [panMemStoreHOL,accessible] at run

/-- A successful structured store retains its actual sequence of word writes. -/
theorem mem_stores_source_domain_extend (values : List (HolWordLab 64))
 (small large : BitVec 64→Prop) [DecidablePred small] [DecidablePred large]
 (subset : ∀a,small a→large a) :
 ∀(address : BitVec 64) (memory output : BitVec 64→HolWordLab 64),
 panMemStoresHOL address values small memory=some output→
 panMemStoresHOL address values large memory=some output := by
 induction values with
 | nil=>intro address memory output run;exact run
 | cons value rest ih=>
  intro address memory output run
  simp only [panMemStoresHOL] at run ⊢
  cases first : panMemStoreHOL address value small memory with
  | none=>simp [first] at run
  | some updated=>
   rw [first] at run
   rw [mem_store_source_domain_extend address value small large subset memory updated first]
   exact ih _ updated output run

/-- Byte stores check their containing word cell. Extending the domain changes
neither that cell's word nor the byte-order-sensitive replacement. -/
theorem mem_store_byte_source_domain_extend (memory output : BitVec 64→HolWordLab 64)
 (small large : BitVec 64→Prop) [DecidablePred small] [DecidablePred large]
 (subset : ∀a,small a→large a) (be : Bool) (address : BitVec 64) (byte : BitVec 8)
 (run : panMemStoreByteWord8HOL memory small be address byte=some output) :
 panMemStoreByteWord8HOL memory large be address byte=some output := by
 cases cell : memory (panByteAlignHOL address) with
 | word value=>
  by_cases accessible : small (panByteAlignHOL address)
  · simpa only [panMemStoreByteWord8HOL,cell,if_pos accessible,
      if_pos (subset _ accessible)] using run
  · simp [panMemStoreByteWord8HOL,cell,accessible] at run

/-- The 32-bit store's alignment requirement is retained exactly; only its
successful containing-cell domain check is transported. -/
theorem mem_store32_source_domain_extend (memory output : BitVec 64→HolWordLab 64)
 (small large : BitVec 64→Prop) [DecidablePred small] [DecidablePred large]
 (subset : ∀a,small a→large a) (be : Bool) (address : BitVec 64) (value : BitVec 32)
 (run : panMemStore32HOL memory small be address value=some output) :
 panMemStore32HOL memory large be address value=some output := by
 by_cases aligned : address.toNat%4=0
 · cases cell : memory (panByteAlignHOL address) with
   | word word=>
    by_cases accessible : small (panByteAlignHOL address)
    · simpa only [panMemStore32HOL,if_pos aligned,cell,if_pos accessible,
        if_pos (subset _ accessible)] using run
    · simp [panMemStore32HOL,aligned,cell,accessible] at run
 · simp [panMemStore32HOL,aligned] at run

#print axioms mem_store_source_domain_extend
#print axioms mem_stores_source_domain_extend
#print axioms mem_store_byte_source_domain_extend
#print axioms mem_store32_source_domain_extend
end InitECandidate.Runtime
