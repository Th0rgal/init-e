import Init
import InitECandidate.Solver.Op3ClockBound
import InitECandidate.Solver.LoopFuel

namespace InitECandidate.Solver.Op3PassInventory
open InitECandidate.Solver.Op3ClockBound
open InitECandidate.Solver.LoopFuel

/-- Inventory size of the pre-existing seven-pass solver cone. -/
def solverModuleCount : Nat := 67

def passModuleCount : Nat := 7

theorem solverModuleCount_eq : solverModuleCount = 67 := rfl
theorem passModuleCount_eq : passModuleCount = 7 := rfl

end InitECandidate.Solver.Op3PassInventory
