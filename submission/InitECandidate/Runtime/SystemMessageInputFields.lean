import InitECandidate.Runtime.SystemMessageExactSetupReach
import InitECandidate.Runtime.AccessTableDeclarationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Actual scalar contents established by the seven system message stores. -/
structure SystemMessageInputs {F : Type} (s : PanSemStateFiniteExact 64 F)
 (message target data dataSize code codeSize : BitVec 64) : Prop where
 gas : s.memory (message+40)=.word 30000000
 stateGas : s.memory (message+48)=.word ((97920#64)*(16#64))
 data : s.memory (message+88)=.word data
 dataSize : s.memory (message+96)=.word dataSize
 target : s.memory (message+104)=.word target
 code : s.memory (message+112)=.word code
 codeSize : s.memory (message+120)=.word codeSize

/-- Exact contents follow from the executed original stores; they are not
assumed interpreter inputs. Distinct offsets cannot alias even under wrapping. -/
theorem system_message_setup_post_inputs {F : Type} (s : PanSemStateFiniteExact 64 F)
 (message target data dataSize code codeSize : BitVec 64) :
 SystemMessageInputs (systemMessageGasSetupPost s message target data dataSize code codeSize)
 message target data dataSize code codeSize := by
 constructor <;>simp [systemMessageGasSetupPost,sourceWriteWord]
/-- Both real table constructors preserve every initialized message input,
because the message ends before the actual allocation frontier. -/
theorem SystemMessageInputs.after_table {F : Type} {s next : PanSemStateFiniteExact 64 F}
 {message target data dataSize code codeSize pointer keyLength : BitVec 64} {name : MlS}
 (inputs : SystemMessageInputs s message target data dataSize code codeSize)
 (lower : message.toNat+176≤pointer.toNat) (capped : pointer.toNat≤33806089496)
 (table : AccessTableReady s name pointer keyLength next) :
 SystemMessageInputs next message target data dataSize code codeSize := by
 have kept (offset : BitVec 64) (inside : offset.toNat<176) : next.memory (message+offset)=s.memory (message+offset) := by
  apply table.2.2.2.2.2.1
  rw [BitVec.toNat_add_of_lt (by omega)]
  omega
 exact ⟨(kept 40 (by decide)).trans inputs.gas,(kept 48 (by decide)).trans inputs.stateGas,
  (kept 88 (by decide)).trans inputs.data,(kept 96 (by decide)).trans inputs.dataSize,
  (kept 104 (by decide)).trans inputs.target,(kept 112 (by decide)).trans inputs.code,
  (kept 120 (by decide)).trans inputs.codeSize⟩

/-- Actual accessed-set pointer stores cannot overwrite the message inputs. -/
theorem SystemMessageInputs.after_access_write {F : Type} {s : PanSemStateFiniteExact 64 F}
 {message target data dataSize code codeSize : BitVec 64}
 (inputs : SystemMessageInputs s message target data dataSize code codeSize) (pointer offset : BitVec 64)
 (access : offset=152 ∨offset=160) :
 SystemMessageInputs (sourceWriteWord s (message+offset) pointer) message target data dataSize code codeSize := by
 rcases access with rfl|rfl
 all_goals constructor <;>simp [sourceWriteWord]
 all_goals first
  | exact inputs.gas
  | exact inputs.stateGas
  | exact inputs.data
  | exact inputs.dataSize
  | exact inputs.target
  | exact inputs.code
  | exact inputs.codeSize
#print axioms system_message_setup_post_inputs
#print axioms SystemMessageInputs.after_table
#print axioms SystemMessageInputs.after_access_write
end InitECandidate.Runtime
