import Leanr
import Leanr.BusInteraction

namespace OpenVM

def busIdExecutionBridge : Nat := 0
def busIdMemory : Nat := 1
def busIdPcLookup : Nat := 2
def busIdVariableRangeChecker : Nat := 3
def busIdBitwiseLookup : Nat := 6
def busIdTupleRangeChecker : Nat := 7

def babyBear : Nat := 0x1dffff

def openVMBusInteractionHandler : BusInteractionHandler babyBear :=
  {
    isBusStateful := fun busId => busId = busIdExecutionBridge || busId = busIdMemory,
    handleBusInteraction := fun bi => bi -- No-op for now
  }

end OpenVM
