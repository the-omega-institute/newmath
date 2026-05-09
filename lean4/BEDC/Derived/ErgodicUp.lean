import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ErgodicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ErgodicBHistSourceSurface [AskSetup] [PackageSetup]
    (dyn measure invariant transport route provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dyn ∧ UnaryHistory measure ∧ UnaryHistory invariant ∧
    UnaryHistory transport ∧ UnaryHistory provenance ∧ Cont invariant transport route ∧
      Cont route provenance endpoint ∧ PkgSig bundle endpoint pkg

def ErgodicMeasurePreservingCarrier [AskSetup] [PackageSetup]
    (dyn measure invariant transport route provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  ErgodicBHistSourceSurface dyn measure invariant transport route provenance endpoint bundle pkg ∧
    Cont dyn measure invariant

theorem ErgodicBHistSourceSurface_invariant_subspace_classifier [AskSetup] [PackageSetup]
    {dyn measure invariant transport route provenance endpoint invariant' transport' route'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ErgodicMeasurePreservingCarrier dyn measure invariant transport route provenance endpoint
        bundle pkg ->
      hsame invariant invariant' ->
        hsame transport transport' ->
          Cont invariant' transport' route' ->
            Cont route' provenance endpoint' ->
              PkgSig bundle endpoint' pkg ->
                ErgodicBHistSourceSurface dyn measure invariant' transport' route' provenance
                    endpoint' bundle pkg ∧
                  hsame route route' ∧ hsame endpoint endpoint' := by
  intro carrier sameInvariant sameTransport routeRow' endpointRow' pkgSig'
  have surface :
      ErgodicBHistSourceSurface dyn measure invariant transport route provenance endpoint
        bundle pkg :=
    carrier.left
  have routeRow : Cont invariant transport route :=
    surface.right.right.right.right.right.left
  have endpointRow : Cont route provenance endpoint :=
    surface.right.right.right.right.right.right.left
  have invariantUnary' : UnaryHistory invariant' :=
    unary_transport surface.right.right.left sameInvariant
  have transportUnary' : UnaryHistory transport' :=
    unary_transport surface.right.right.right.left sameTransport
  have routeSame : hsame route route' :=
    cont_respects_hsame sameInvariant sameTransport routeRow routeRow'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame routeSame (hsame_refl provenance) endpointRow endpointRow'
  exact And.intro
    (And.intro surface.left
      (And.intro surface.right.left
        (And.intro invariantUnary'
          (And.intro transportUnary'
            (And.intro surface.right.right.right.right.left
              (And.intro routeRow' (And.intro endpointRow' pkgSig')))))))
    (And.intro routeSame endpointSame)

end BEDC.Derived.ErgodicUp
