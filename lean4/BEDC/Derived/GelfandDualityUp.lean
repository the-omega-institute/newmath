import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GelfandDualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GelfandDualitySpectrumPairingCarrier [AskSetup] [PackageSetup]
    (A X character evaluation rhoA rhoX provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory A ∧ UnaryHistory X ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧
    UnaryHistory provenance ∧ hsame rhoA A ∧ hsame rhoX X ∧
      Cont character evaluation ledger ∧ Cont ledger provenance endpoint ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem GelfandDualitySpectrum_source_obligation [AskSetup] [PackageSetup]
    {A X character evaluation rhoA rhoX provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      UnaryHistory A ∧ UnaryHistory X ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧
        hsame rhoA A ∧ hsame rhoX X ∧ Cont character evaluation ledger ∧
          Cont ledger provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    ⟨carrier.left, carrier.right.left, carrier.right.right.left,
      carrier.right.right.right.left, carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right⟩

theorem GelfandDualitySpectrumPairingCarrier_source_obligation [AskSetup] [PackageSetup]
    {A X character evaluation rhoA rhoX provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      UnaryHistory A ∧ UnaryHistory X ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧
        hsame rhoA A ∧ hsame rhoX X ∧ Cont character evaluation ledger ∧
          Cont provenance ledger endpoint ∧ hsame endpoint (append provenance ledger) := by
  intro carrier
  exact
    ⟨carrier.left, carrier.right.left, carrier.right.right.left,
      carrier.right.right.right.left, carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.left⟩

end BEDC.Derived.GelfandDualityUp
