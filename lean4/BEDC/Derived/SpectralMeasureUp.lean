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

def SpectralMeasurePacket [AskSetup] [PackageSetup]
    (hilbert observable event projection orthogonality finiteAdd route provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory observable ∧ UnaryHistory event ∧
    UnaryHistory projection ∧ UnaryHistory orthogonality ∧ UnaryHistory finiteAdd ∧
      Cont event projection route ∧ Cont orthogonality finiteAdd endpoint ∧
        Cont provenance route endpoint ∧ PkgSig bundle endpoint pkg

theorem SpectralMeasurePacket_hsame_stability [AskSetup] [PackageSetup]
    {hilbert observable event projection orthogonality finiteAdd route provenance endpoint
      hilbert' observable' event' projection' orthogonality' finiteAdd' route' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasurePacket hilbert observable event projection orthogonality finiteAdd route
        provenance endpoint bundle pkg ->
      hsame hilbert hilbert' -> hsame observable observable' -> hsame event event' ->
        hsame projection projection' -> hsame orthogonality orthogonality' ->
          hsame finiteAdd finiteAdd' -> Cont event' projection' route' ->
            Cont orthogonality' finiteAdd' endpoint' -> Cont provenance route' endpoint' ->
              PkgSig bundle endpoint' pkg ->
                SpectralMeasurePacket hilbert' observable' event' projection' orthogonality'
                    finiteAdd' route' provenance endpoint' bundle pkg ∧
                  hsame route route' ∧ hsame endpoint endpoint' := by
  intro packet sameHilbert sameObservable sameEvent sameProjection sameOrthogonality
    sameFiniteAdd routeCont' endpointCont' provenanceCont' pkgSig'
  have hilbertUnary' : UnaryHistory hilbert' :=
    unary_transport packet.left sameHilbert
  have observableUnary' : UnaryHistory observable' :=
    unary_transport packet.right.left sameObservable
  have eventUnary' : UnaryHistory event' :=
    unary_transport packet.right.right.left sameEvent
  have projectionUnary' : UnaryHistory projection' :=
    unary_transport packet.right.right.right.left sameProjection
  have orthogonalityUnary' : UnaryHistory orthogonality' :=
    unary_transport packet.right.right.right.right.left sameOrthogonality
  have finiteAddUnary' : UnaryHistory finiteAdd' :=
    unary_transport packet.right.right.right.right.right.left sameFiniteAdd
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameEvent sameProjection
      packet.right.right.right.right.right.right.left routeCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameOrthogonality sameFiniteAdd
      packet.right.right.right.right.right.right.right.left endpointCont'
  exact
    ⟨⟨hilbertUnary', observableUnary', eventUnary', projectionUnary', orthogonalityUnary',
        finiteAddUnary', routeCont', endpointCont', provenanceCont', pkgSig'⟩,
      sameRoute, sameEndpoint⟩

end BEDC.Derived.SpectralMeasureUp
