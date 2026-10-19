import InitECandidate.Runtime.HtrWithdrawalSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Fixed record hashes use only these three bounded hashing/copy operations. -/
inductive RecordHashStep where
  | vector (inputOffset length outputOffset : BitVec 64)
  | copy (inputOffset outputOffset : BitVec 64)
  | uint (inputOffset outputOffset : BitVec 64)

def recordHashAddress (name : MlS) (offset : BitVec 64) : ExpHOL 64 :=
  if offset = 0 then .var .local name else .op .add [.var .local name,.const offset]

def RecordHashStep.function : RecordHashStep → MlS
  | .vector _ _ _ => ofString "htr_bytes_vector"
  | .copy _ _ => ofString "memcpy"
  | .uint _ _ => ofString "htr_u64_at"

def RecordHashStep.arguments : RecordHashStep → List (ExpHOL 64)
  | .vector i n o => [recordHashAddress (ofString "e") i,.const n,recordHashAddress (ofString "ch") o]
  | .copy i o => [recordHashAddress (ofString "ch") o,recordHashAddress (ofString "e") i,.const 32]
  | .uint i o => [recordHashAddress (ofString "e") i,recordHashAddress (ofString "ch") o]

def RecordHashStep.cost : RecordHashStep → Nat
  | .vector _ _ _ => htrBytesVectorBodyCost + 1
  | .copy _ _ => 16
  | .uint _ _ => 30

def RecordHashStep.Small : RecordHashStep → Prop
  | .vector _ n _ => n.toNat ≤ 134217712
  | _ => True

def recordHashFinish (count : BitVec 64) : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "merkleize")
    [.var .local (ofString "ch"),.const count,.const count,.var .local (ofString "out")])
    (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) (.return (.const 0)))

def recordHashSuffix : List RecordHashStep → BitVec 64 → ProgHOL 64
  | [],n => recordHashFinish n
  | step :: rest,n => .seq (.call (some (none,none)) step.function step.arguments) (recordHashSuffix rest n)

def recordHashCost : List RecordHashStep → Nat
  | [] => (merkleBodyCost + 1) + 1
  | step :: rest => step.cost + recordHashCost rest

def recordHashBody (count : BitVec 64) (steps : List RecordHashStep) : ProgHOL 64 :=
  .decCall (ofString "mark") .one (ofString "heap_mark") []
    (.decCall (ofString "ch") .one (ofString "alloc") [.panop .mul [.const count,.const 32]] (recordHashSuffix steps count))

def depositHashSteps : List RecordHashStep :=
  [.vector 0 48 0,.copy 48 32,.uint 80 64,.vector 88 96 96,.uint 184 128]
def wdreqHashSteps : List RecordHashStep :=
  [.vector 0 20 0,.vector 20 48 32,.uint 68 64]
def consHashSteps : List RecordHashStep :=
  [.vector 0 20 0,.vector 20 48 32,.vector 68 48 64]
def bdepHashSteps : List RecordHashStep :=
  [.vector 0 48 0,.copy 48 32,.uint 80 64,.vector 88 96 96]
def bexitHashSteps : List RecordHashStep :=
  [.vector 0 20 0,.vector 20 48 32]

theorem source_htrDeposit_record : structuralFunctionBody Guest.guestFn_htr_deposit = recordHashBody 5 depositHashSteps := by rfl
theorem source_htrWdreq_record : structuralFunctionBody Guest.guestFn_htr_wdreq = recordHashBody 3 wdreqHashSteps := by rfl
theorem source_htrCons_record : structuralFunctionBody Guest.guestFn_htr_cons = recordHashBody 3 consHashSteps := by rfl
theorem source_htrBdep_record : structuralFunctionBody Guest.guestFn_htr_bdep = recordHashBody 4 bdepHashSteps := by rfl
theorem source_htrBexit_record : structuralFunctionBody Guest.guestFn_htr_bexit = recordHashBody 2 bexitHashSteps := by rfl

#print axioms source_htrDeposit_record
#print axioms source_htrWdreq_record
#print axioms source_htrCons_record
#print axioms source_htrBdep_record
#print axioms source_htrBexit_record
end InitECandidate.Runtime
