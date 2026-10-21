import Init

namespace BoundedTableExperiment

/-- Half-open address interval `[a, a+n)`. -/
def InRegion (a n x : Nat) : Prop := a ≤ x ∧ x < a + n

/-- Two half-open regions do not overlap. -/
def Disjoint (a n b m : Nat) : Prop := a + n ≤ b ∨ b + m ≤ a

theorem not_in_both_of_disjoint (a n b m x : Nat) (h : Disjoint a n b m)
    (ha : InRegion a n x) (hb : InRegion b m x) : False := by
  unfold Disjoint at h
  unfold InRegion at ha hb
  omega

/-- One `st path + depth*8, node` footprint lies inside a path buffer of
`size` bytes once `depth+1` slots are reserved. -/
theorem path_store_in_region (base size depth : Nat)
    (hsize : (depth + 1) * 8 ≤ size) :
    InRegion base size (base + depth * 8) ∧
      InRegion (base + depth * 8) 8 (base + depth * 8) := by
  unfold InRegion
  constructor
  · constructor <;> omega
  · constructor <;> omega

/-- A binary-search read at `mid < depth` lies inside the recorded path. -/
theorem path_read_in_region (base size mid depth : Nat)
    (hsize : depth * 8 ≤ size) (hmid : mid < depth) :
    InRegion base size (base + mid * 8) := by
  unfold InRegion
  constructor <;> omega

/-- Concrete no-alias lemma for the path buffer versus one other table
region. -/
theorem path_store_no_alias (pbase psize obase osize depth : Nat)
    (hdisj : Disjoint pbase psize obase osize)
    (hpsize : (depth + 1) * 8 ≤ psize)
    (hother : InRegion obase osize (pbase + depth * 8)) : False := by
  have hp : InRegion pbase psize (pbase + depth * 8) :=
    (path_store_in_region pbase psize depth hpsize).1
  exact not_in_both_of_disjoint pbase psize obase osize _ hdisj hp hother

/-- The four regions a path store must avoid. -/
structure PathSafe (pbase psize kbase ksize nbase nsize obase osize sbase ssize : Nat) : Prop where
  keys : Disjoint pbase psize kbase ksize
  nodes : Disjoint pbase psize nbase nsize
  output : Disjoint pbase psize obase osize
  scratch : Disjoint pbase psize sbase ssize

theorem path_store_no_alias_all (pbase psize kbase ksize nbase nsize obase osize
    sbase ssize depth : Nat) (hsafe : PathSafe pbase psize kbase ksize nbase nsize
      obase osize sbase ssize) (hpsize : (depth + 1) * 8 ≤ psize) :
    ¬ InRegion kbase ksize (pbase + depth * 8) ∧
    ¬ InRegion nbase nsize (pbase + depth * 8) ∧
    ¬ InRegion obase osize (pbase + depth * 8) ∧
    ¬ InRegion sbase ssize (pbase + depth * 8) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun hk => path_store_no_alias pbase psize kbase ksize depth hsafe.keys hpsize hk
  · exact fun hn => path_store_no_alias pbase psize nbase nsize depth hsafe.nodes hpsize hn
  · exact fun ho => path_store_no_alias pbase psize obase osize depth hsafe.output hpsize ho
  · exact fun hs => path_store_no_alias pbase psize sbase ssize depth hsafe.scratch hpsize hs

end BoundedTableExperiment

#print axioms BoundedTableExperiment.path_store_no_alias_all
#print axioms BoundedTableExperiment.path_read_in_region
