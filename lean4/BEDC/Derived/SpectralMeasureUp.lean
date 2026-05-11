import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpectralMeasureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SpectralMeasureCarrier [AskSetup] [PackageSetup]
    (hilbert observable event projection orthogonality additivity route provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory observable ∧ UnaryHistory event ∧
    UnaryHistory projection ∧ UnaryHistory orthogonality ∧ UnaryHistory additivity ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ Cont hilbert observable projection ∧
        Cont event projection route ∧ Cont orthogonality additivity provenance ∧
          PkgSig bundle provenance pkg

theorem SpectralMeasureCarrier_hsame_stability [AskSetup] [PackageSetup]
    {hilbert observable event projection orthogonality additivity route provenance hilbert'
      observable' event' projection' orthogonality' additivity' route' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasureCarrier hilbert observable event projection orthogonality additivity route
        provenance bundle pkg ->
      hsame hilbert hilbert' ->
        hsame observable observable' ->
          hsame event event' ->
            hsame orthogonality orthogonality' ->
              hsame additivity additivity' ->
                Cont hilbert' observable' projection' ->
                  Cont event' projection' route' ->
                    Cont orthogonality' additivity' provenance' ->
                      PkgSig bundle provenance' pkg ->
                        SpectralMeasureCarrier hilbert' observable' event' projection'
                            orthogonality' additivity' route' provenance' bundle pkg ∧
                          hsame projection projection' ∧ hsame route route' ∧
                            hsame provenance provenance' := by
  intro carrier sameHilbert sameObservable sameEvent sameOrthogonality sameAdditivity
    projectionRow' routeRow' provenanceRow' pkg'
  have hilbertUnary' : UnaryHistory hilbert' :=
    unary_transport carrier.left sameHilbert
  have observableUnary' : UnaryHistory observable' :=
    unary_transport carrier.right.left sameObservable
  have eventUnary' : UnaryHistory event' :=
    unary_transport carrier.right.right.left sameEvent
  have orthogonalityUnary' : UnaryHistory orthogonality' :=
    unary_transport carrier.right.right.right.right.left sameOrthogonality
  have additivityUnary' : UnaryHistory additivity' :=
    unary_transport carrier.right.right.right.right.right.left sameAdditivity
  have sameProjection : hsame projection projection' :=
    cont_respects_hsame sameHilbert sameObservable
      carrier.right.right.right.right.right.right.right.right.left projectionRow'
  have projectionUnary' : UnaryHistory projection' :=
    unary_cont_closed hilbertUnary' observableUnary' projectionRow'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameEvent sameProjection
      carrier.right.right.right.right.right.right.right.right.right.left routeRow'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed eventUnary' projectionUnary' routeRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameOrthogonality sameAdditivity
      carrier.right.right.right.right.right.right.right.right.right.right.left
      provenanceRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed orthogonalityUnary' additivityUnary' provenanceRow'
  exact
    And.intro
      (And.intro hilbertUnary'
        (And.intro observableUnary'
          (And.intro eventUnary'
            (And.intro projectionUnary'
              (And.intro orthogonalityUnary'
                (And.intro additivityUnary'
                  (And.intro routeUnary'
                    (And.intro provenanceUnary'
                      (And.intro projectionRow'
                        (And.intro routeRow'
                          (And.intro provenanceRow' pkg')))))))))))
      (And.intro sameProjection (And.intro sameRoute sameProvenance))

end BEDC.Derived.SpectralMeasureUp
