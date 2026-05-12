import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyTailComparisonCarrier [AskSetup] [PackageSetup]
    (leftName rightName modulus window endpointLedger readback provenance namecert endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftName ∧
    UnaryHistory rightName ∧
    UnaryHistory modulus ∧
    UnaryHistory window ∧
    UnaryHistory endpointLedger ∧
    UnaryHistory readback ∧
    UnaryHistory provenance ∧
    UnaryHistory namecert ∧
    UnaryHistory endpoint ∧
    Cont (append leftName rightName) modulus window ∧
    Cont window endpointLedger readback ∧
    hsame endpoint (append readback provenance) ∧
    hsame namecert endpoint ∧
    PkgSig bundle endpoint pkg

theorem CauchyTailComparisonCarrier_tail_stability [AskSetup] [PackageSetup]
    {leftName rightName modulus window endpointLedger readback provenance namecert endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCarrier leftName rightName modulus window endpointLedger readback
      provenance namecert endpoint bundle pkg →
      Cont (append leftName rightName) modulus window ∧
        Cont window endpointLedger readback ∧
          hsame endpoint (append readback provenance) ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  cases carrier with
  | intro _leftUnary rest =>
      cases rest with
      | intro _rightUnary rest =>
          cases rest with
          | intro _modulusUnary rest =>
              cases rest with
              | intro _windowUnary rest =>
                  cases rest with
                  | intro _endpointLedgerUnary rest =>
                      cases rest with
                      | intro _readbackUnary rest =>
                          cases rest with
                          | intro _provenanceUnary rest =>
                              cases rest with
                              | intro _namecertUnary rest =>
                                  cases rest with
                                  | intro _endpointUnary rest =>
                                      cases rest with
                                      | intro commonWindow rest =>
                                          cases rest with
                                          | intro endpointReadback rest =>
                                              cases rest with
                                              | intro endpointSame rest =>
                                                  cases rest with
                                                  | intro _namecertSame pkgSig =>
                                                      exact And.intro commonWindow
                                                        (And.intro endpointReadback
                                                          (And.intro endpointSame pkgSig))

end BEDC.Derived.CauchyTailComparisonUp
