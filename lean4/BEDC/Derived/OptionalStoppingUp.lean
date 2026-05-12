import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OptionalStoppingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def OptionalStoppingCarrier [AskSetup] [PackageSetup]
    (prob process stopping bound stoppedValue filtration integrability sameRows route provenance
      namecert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prob ∧
    UnaryHistory process ∧
    UnaryHistory stopping ∧
    UnaryHistory bound ∧
    UnaryHistory stoppedValue ∧
    UnaryHistory filtration ∧
    UnaryHistory integrability ∧
    UnaryHistory sameRows ∧
    UnaryHistory route ∧
    UnaryHistory provenance ∧
    UnaryHistory namecert ∧
    UnaryHistory endpoint ∧
    Cont stopping bound stoppedValue ∧
    Cont process filtration integrability ∧
    hsame sameRows (append prob process) ∧
    hsame route (append stopping bound) ∧
    hsame provenance (append stoppedValue integrability) ∧
    hsame endpoint (append stoppedValue integrability) ∧
    hsame namecert endpoint ∧
    PkgSig bundle endpoint pkg

theorem OptionalStoppingCarrier_bounded_stopped_value_readback [AskSetup] [PackageSetup]
    {prob process stopping bound stoppedValue filtration integrability sameRows route provenance
      namecert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptionalStoppingCarrier prob process stopping bound stoppedValue filtration integrability sameRows
      route provenance namecert endpoint bundle pkg →
      Cont stopping bound stoppedValue ∧
        Cont process filtration integrability ∧
          hsame endpoint (append stoppedValue integrability) ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  cases carrier with
  | intro _probUnary rest =>
      cases rest with
      | intro _processUnary rest =>
          cases rest with
          | intro _stoppingUnary rest =>
              cases rest with
              | intro _boundUnary rest =>
                  cases rest with
                  | intro _stoppedValueUnary rest =>
                      cases rest with
                      | intro _filtrationUnary rest =>
                          cases rest with
                          | intro _integrabilityUnary rest =>
                              cases rest with
                              | intro _sameRowsUnary rest =>
                                  cases rest with
                                  | intro _routeUnary rest =>
                                      cases rest with
                                      | intro _provenanceUnary rest =>
                                          cases rest with
                                          | intro _namecertUnary rest =>
                                              cases rest with
                                              | intro _endpointUnary rest =>
                                                  cases rest with
                                                  | intro stoppedValueReadback rest =>
                                                      cases rest with
                                                      | intro integrabilityReadback rest =>
                                                          cases rest with
                                                          | intro _sameRows rest =>
                                                              cases rest with
                                                              | intro _route rest =>
                                                                  cases rest with
                                                                  | intro _provenance rest =>
                                                                      cases rest with
                                                                      | intro endpointSame rest =>
                                                                          cases rest with
                                                                          | intro _namecertSame pkgSig =>
                                                                              exact And.intro
                                                                                stoppedValueReadback
                                                                                (And.intro
                                                                                  integrabilityReadback
                                                                                  (And.intro
                                                                                    endpointSame
                                                                                    pkgSig))

end BEDC.Derived.OptionalStoppingUp
