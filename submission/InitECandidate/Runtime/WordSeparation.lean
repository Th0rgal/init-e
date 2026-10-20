import InitECandidate.Runtime.TriePathBuffer
namespace InitECandidate.Runtime.WordSep
open Flapjack Flapjack.PanSemStateFiniteExact
abbrev Address := BitVec 64
abbrev Memory := Address→HolWordLab 64

/-- A fixed-footprint assertion is insensitive to all other memory words.
Addresses are semantic word cells, so byte buffers own their containing cells. -/
structure Assertion where
 footprint : Set Address
 holds : Memory→Prop
 stable : ∀before after, (∀address∈footprint,after address=before address)→holds before→holds after

/-- Separating conjunction requires disjoint footprints and both assertions. -/
def sep (left right : Assertion) : Assertion where
 footprint := left.footprint ∪right.footprint
 holds := fun memory=>Disjoint left.footprint right.footprint ∧left.holds memory ∧right.holds memory
 stable := by
  intro before after same facts
  exact ⟨facts.1,left.stable before after (fun a h=>same a (Or.inl h)) facts.2.1,
   right.stable before after (fun a h=>same a (Or.inr h)) facts.2.2⟩

def snapshot (cells : Set Address) (original : Memory) : Assertion where
 footprint := cells
 holds := fun memory=>∀address∈cells,memory address=original address
 stable := by
  intro before after same facts address member
  exact (same address member).trans (facts address member)

def pointsTo (address : Address) (value : HolWordLab 64) : Assertion where
 footprint := {address}
 holds := fun memory=>memory address=value
 stable := by
  intro before after same fact
  exact (same address (Set.mem_singleton address)).trans fact

def WritesOnly (cells : Set Address) (before after : Memory) : Prop :=
 ∀address,address∉cells→after address=before address

/-- The footprint frame rule applies to the actual execution's write effect;
no execution result, successful call, or resource bound is assumed here. -/
theorem frame (assertion : Assertion) {writes : Set Address} {before after : Memory}
 (effect : WritesOnly writes before after) (separate : Disjoint writes assertion.footprint)
 (fact : assertion.holds before) : assertion.holds after := by
 apply assertion.stable before after _ fact
 intro address owned
 apply effect
 intro written
 exact Set.disjoint_left.mp separate written owned

theorem sep_comm (left right : Assertion) (memory : Memory) :
 (sep left right).holds memory ↔(sep right left).holds memory := by
 constructor <;>intro h <;>exact ⟨h.1.symm,h.2.2,h.2.1⟩

#print axioms frame
#print axioms sep_comm
end InitECandidate.Runtime.WordSep
