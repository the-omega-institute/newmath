import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def DyadicRatCorePacket
    (_mantissa exponent ledger provenance denominator window packet : BHist) : Prop :=
  UnaryHistory exponent ∧ Cont exponent ledger denominator ∧
    Cont denominator provenance window ∧ hsame packet window

theorem DyadicRatCorePacket_denominator_ledger_transport
    {mantissa mantissa' exponent exponent' ledger ledger' provenance provenance' denominator
      denominator' window window' packet packet' : BHist}
    (hD : DyadicRatCorePacket mantissa exponent ledger provenance denominator window packet)
    (sameMantissa : hsame mantissa mantissa') (sameExponent : hsame exponent exponent')
    (sameLedger : hsame ledger ledger') (sameProvenance : hsame provenance provenance')
    (sameDenominator : hsame denominator denominator') (sameWindow : hsame window window')
    (samePacket : hsame packet packet') :
    DyadicRatCorePacket mantissa' exponent' ledger' provenance' denominator' window' packet' ∧
      Cont exponent' ledger' denominator' ∧ Cont denominator' provenance' window' := by
  cases sameMantissa
  cases sameExponent
  cases sameLedger
  cases sameProvenance
  cases sameDenominator
  cases sameWindow
  cases samePacket
  exact And.intro hD (And.intro hD.right.left hD.right.right.left)

end BEDC.Derived.DyadicRatCoreUp
