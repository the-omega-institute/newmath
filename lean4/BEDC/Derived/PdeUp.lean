import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PdeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PdeCarriedSourceRow [AskSetup] [PackageSetup]
    (manifold derivative relation boundary endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory derivative ∧ UnaryHistory boundary ∧
    Cont manifold derivative relation ∧ Cont relation boundary endpoint ∧
      PkgSig bundle endpoint pkg

theorem PdeCarriedSourceRow_carrier_obligation [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      UnaryHistory relation ∧ UnaryHistory endpoint ∧ Cont manifold derivative relation ∧
        Cont relation boundary endpoint ∧ PkgSig bundle endpoint pkg := by
  intro row
  have relationUnary : UnaryHistory relation :=
    unary_cont_closed row.left row.right.left row.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed relationUnary row.right.right.left row.right.right.right.right.left
  exact And.intro relationUnary
    (And.intro endpointUnary
      (And.intro row.right.right.right.left
        (And.intro row.right.right.right.right.left row.right.right.right.right.right)))

theorem PdeCarriedSourceRow_classifier_obligation [AskSetup] [PackageSetup]
    {manifold manifold' derivative derivative' relation relation' boundary boundary'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      UnaryHistory manifold' -> UnaryHistory derivative' -> UnaryHistory boundary' ->
        hsame manifold manifold' -> hsame derivative derivative' -> hsame boundary boundary' ->
          Cont manifold' derivative' relation' -> Cont relation' boundary' endpoint' ->
            UnaryHistory relation' ∧ UnaryHistory endpoint' ∧
              hsame relation relation' ∧ hsame endpoint endpoint' := by
  intro row manifoldUnary' derivativeUnary' boundaryUnary' sameManifold sameDerivative
    sameBoundary relationCont' endpointCont'
  have relationUnary' : UnaryHistory relation' :=
    unary_cont_closed manifoldUnary' derivativeUnary' relationCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed relationUnary' boundaryUnary' endpointCont'
  have sameRelation : hsame relation relation' :=
    cont_respects_hsame sameManifold sameDerivative row.right.right.right.left relationCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRelation sameBoundary row.right.right.right.right.left endpointCont'
  exact And.intro relationUnary'
    (And.intro endpointUnary' (And.intro sameRelation sameEndpoint))

theorem PdeCarriedSourceRow_ledger_exactness_surface
    {manifold derivative relation boundary relationBoundary endpoint : BHist} :
    UnaryHistory manifold -> UnaryHistory derivative -> UnaryHistory relation ->
      UnaryHistory boundary -> Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary endpoint ->
          UnaryHistory relationBoundary ∧ UnaryHistory endpoint ∧
            Cont relation boundary relationBoundary ∧
              Cont (append manifold derivative) relationBoundary endpoint := by
  intro manifoldUnary derivativeUnary relationUnary boundaryUnary relationBoundaryCont endpointCont
  have relationBoundaryUnary : UnaryHistory relationBoundary :=
    unary_cont_closed relationUnary boundaryUnary relationBoundaryCont
  have manifoldDerivativeUnary : UnaryHistory (append manifold derivative) :=
    unary_append_closed manifoldUnary derivativeUnary
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed manifoldDerivativeUnary relationBoundaryUnary endpointCont
  exact And.intro relationBoundaryUnary
    (And.intro endpointUnary (And.intro relationBoundaryCont endpointCont))

theorem PdeCarriedSourceRow_stability_ledger_exactness_obligation [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint relationBoundary summarizedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary summarizedEndpoint ->
          UnaryHistory relationBoundary ∧ UnaryHistory summarizedEndpoint ∧
            hsame relationBoundary endpoint ∧ Cont relation boundary relationBoundary ∧
              Cont (append manifold derivative) relationBoundary summarizedEndpoint ∧
                PkgSig bundle endpoint pkg := by
  intro row relationBoundaryCont summarizedEndpointCont
  have relationUnary : UnaryHistory relation :=
    unary_cont_closed row.left row.right.left row.right.right.right.left
  have relationBoundaryUnary : UnaryHistory relationBoundary :=
    unary_cont_closed relationUnary row.right.right.left relationBoundaryCont
  have manifoldDerivativeUnary : UnaryHistory (append manifold derivative) :=
    unary_append_closed row.left row.right.left
  have summarizedEndpointUnary : UnaryHistory summarizedEndpoint :=
    unary_cont_closed manifoldDerivativeUnary relationBoundaryUnary summarizedEndpointCont
  have sameEndpoint : hsame relationBoundary endpoint :=
    cont_deterministic relationBoundaryCont row.right.right.right.right.left
  exact And.intro relationBoundaryUnary
    (And.intro summarizedEndpointUnary
      (And.intro sameEndpoint
        (And.intro relationBoundaryCont
          (And.intro summarizedEndpointCont row.right.right.right.right.right))))

end BEDC.Derived.PdeUp
