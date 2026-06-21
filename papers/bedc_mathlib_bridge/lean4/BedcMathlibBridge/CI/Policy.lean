import BedcGate.Audit
import BedcMathlibBridge.All

namespace BedcMathlibBridge.CI

def policy : BedcGate.Policy where
  bridgeDeclPrefix := `BedcMathlibBridge
  bridgeModulePrefix := `BedcMathlibBridge
  bedcDeclPrefix := `BEDC
  bedcModulePrefix := `BEDC
  trackedTypeHeads := #[
    `BedcMathlibBridge.Constructive.Int.CInt
  ]
  operationClasses := #[
    `Zero, `One, `Add, `Neg, `Sub, `Mul, `LE
  ]
  provenanceCutpoints := #[
    `BedcMathlibBridge.Constructive.Int.toInt,
    `BedcMathlibBridge.Constructive.Int.ofInt,
    `BedcMathlibBridge.Constructive.Int.CInt.toInt,
    `BedcMathlibBridge.Constructive.Int.CInt.ofInt
  ]
  ignoredDeclPrefixes := #[
    `BedcMathlibBridge.Audit,
    `BedcMathlibBridge.CI
  ]

end BedcMathlibBridge.CI
