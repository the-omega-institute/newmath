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
        PkgSig bundle endpoint pkg

theorem GelfandDualitySpectrum_source_obligation [AskSetup] [PackageSetup]
    {A X character evaluation rhoA rhoX provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      UnaryHistory A ∧ UnaryHistory X ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧
        hsame rhoA A ∧ hsame rhoX X ∧ Cont character evaluation ledger ∧
          Cont ledger provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have unaryA : UnaryHistory A :=
    carrier.left
  have unaryX : UnaryHistory X :=
    carrier.right.left
  have unaryCharacter : UnaryHistory character :=
    carrier.right.right.left
  have unaryEvaluation : UnaryHistory evaluation :=
    carrier.right.right.right.left
  have sameRhoA : hsame rhoA A :=
    carrier.right.right.right.right.right.left
  have sameRhoX : hsame rhoX X :=
    carrier.right.right.right.right.right.right.left
  have characterEvaluationLedger : Cont character evaluation ledger :=
    carrier.right.right.right.right.right.right.right.left
  have ledgerEndpoint : Cont ledger provenance endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  exact And.intro unaryA
    (And.intro unaryX
      (And.intro unaryCharacter
        (And.intro unaryEvaluation
          (And.intro sameRhoA
            (And.intro sameRhoX
              (And.intro characterEvaluationLedger
                (And.intro ledgerEndpoint pkgSig)))))))

end BEDC.Derived.GelfandDualityUp
