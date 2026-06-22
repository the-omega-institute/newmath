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
    `Zero, `One, `Add, `Neg, `Sub, `Mul, `LE, `LT, `LinearOrder, `Dvd,
    `PartialOrder, `DecidableEq, `DecidableLE, `DecidableLT
  ]
  allowedPrimitivePrefixes := #[
    `BedcMathlibBridge.Constructive.Int.CInt
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
  transportDenylist := #[
    `Function.Injective,
    `Function.Surjective,
    `Classical.choice,
    `Quot.sound,
    `propext
  ]

end BedcMathlibBridge.CI
