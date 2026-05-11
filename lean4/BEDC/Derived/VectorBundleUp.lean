import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VectorBundleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def VectorBundleFiniteCarrier [AskSetup] [PackageSetup]
    (bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance
      endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundleRow ∧ UnaryHistory vecspace ∧ UnaryHistory trivialization ∧
    UnaryHistory fibre ∧ UnaryHistory transition ∧ UnaryHistory overlap ∧
      UnaryHistory linearity ∧ UnaryHistory contRows ∧ UnaryHistory provenance ∧
        UnaryHistory endpoint ∧ Cont bundleRow vecspace trivialization ∧
          Cont trivialization overlap transition ∧ Cont transition linearity contRows ∧
            Cont provenance contRows endpoint ∧ PkgSig probe endpoint pkg

theorem VectorBundleFiniteCarrier_classifier_stability_obligation [AskSetup] [PackageSetup]
    {bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance
      endpoint bundleRow' vecspace' trivialization' fibre' transition' overlap' linearity'
      contRows' endpoint' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap linearity
        contRows provenance endpoint probe pkg ->
      hsame bundleRow bundleRow' -> hsame vecspace vecspace' ->
        hsame fibre fibre' -> hsame overlap overlap' -> hsame linearity linearity' ->
          Cont bundleRow' vecspace' trivialization' ->
            Cont trivialization' overlap' transition' ->
              Cont transition' linearity' contRows' ->
                Cont provenance contRows' endpoint' -> PkgSig probe endpoint' pkg ->
                  VectorBundleFiniteCarrier bundleRow' vecspace' trivialization' fibre'
                      transition' overlap' linearity' contRows' provenance endpoint' probe pkg ∧
                    hsame trivialization trivialization' ∧ hsame transition transition' ∧
                      hsame contRows contRows' ∧ hsame endpoint endpoint' := by
  intro carrier sameBundleRow sameVecspace sameFibre sameOverlap sameLinearity
    bundleVecspaceRow trivializationOverlapRow transitionLinearityRow provenanceContRowsRow pkgSig'
  obtain ⟨bundleUnary, vecspaceUnary, trivializationUnary, fibreUnary, transitionUnary,
    overlapUnary, linearityUnary, contRowsUnary, provenanceUnary, endpointUnary,
    bundleVecspaceSource, trivializationOverlapSource, transitionLinearitySource,
    provenanceContRowsSource, _pkgSig⟩ := carrier
  have bundleUnary' : UnaryHistory bundleRow' :=
    unary_transport bundleUnary sameBundleRow
  have vecspaceUnary' : UnaryHistory vecspace' :=
    unary_transport vecspaceUnary sameVecspace
  have trivializationSame : hsame trivialization trivialization' :=
    cont_respects_hsame sameBundleRow sameVecspace bundleVecspaceSource bundleVecspaceRow
  have trivializationUnary' : UnaryHistory trivialization' :=
    unary_transport trivializationUnary trivializationSame
  have fibreUnary' : UnaryHistory fibre' :=
    unary_transport fibreUnary sameFibre
  have overlapUnary' : UnaryHistory overlap' :=
    unary_transport overlapUnary sameOverlap
  have transitionSame : hsame transition transition' :=
    cont_respects_hsame trivializationSame sameOverlap trivializationOverlapSource
      trivializationOverlapRow
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary transitionSame
  have linearityUnary' : UnaryHistory linearity' :=
    unary_transport linearityUnary sameLinearity
  have contRowsSame : hsame contRows contRows' :=
    cont_respects_hsame transitionSame sameLinearity transitionLinearitySource
      transitionLinearityRow
  have contRowsUnary' : UnaryHistory contRows' :=
    unary_transport contRowsUnary contRowsSame
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) contRowsSame provenanceContRowsSource
      provenanceContRowsRow
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary endpointSame
  exact And.intro
    (And.intro bundleUnary'
      (And.intro vecspaceUnary'
        (And.intro trivializationUnary'
          (And.intro fibreUnary'
            (And.intro transitionUnary'
              (And.intro overlapUnary'
                (And.intro linearityUnary'
                  (And.intro contRowsUnary'
                    (And.intro provenanceUnary
                      (And.intro endpointUnary'
                        (And.intro bundleVecspaceRow
                          (And.intro trivializationOverlapRow
                            (And.intro transitionLinearityRow
                              (And.intro provenanceContRowsRow pkgSig'))))))))))))))
    (And.intro trivializationSame
      (And.intro transitionSame (And.intro contRowsSame endpointSame)))

theorem VectorBundleFiniteCarrier_transition_ledger_exactness [AskSetup] [PackageSetup]
    {bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance
      endpoint transition' contRows' endpoint' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap linearity
        contRows provenance endpoint probe pkg ->
      hsame transition transition' -> Cont trivialization overlap transition' ->
        Cont transition' linearity contRows' -> Cont provenance contRows' endpoint' ->
          PkgSig probe endpoint' pkg ->
            VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition' overlap
                linearity contRows' provenance endpoint' probe pkg ∧
              hsame contRows contRows' ∧ hsame endpoint endpoint' := by
  intro carrier sameTransition trivializationOverlapRow transitionLinearityRow
    provenanceContRowsRow pkgSig'
  obtain ⟨bundleUnary, vecspaceUnary, trivializationUnary, fibreUnary, transitionUnary,
    overlapUnary, linearityUnary, contRowsUnary, provenanceUnary, endpointUnary,
    bundleVecspaceRow, trivializationOverlapSource, transitionLinearitySource,
    provenanceContRowsSource, _pkgSig⟩ := carrier
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have contRowsSame : hsame contRows contRows' :=
    cont_respects_hsame sameTransition (hsame_refl linearity) transitionLinearitySource
      transitionLinearityRow
  have contRowsUnary' : UnaryHistory contRows' :=
    unary_transport contRowsUnary contRowsSame
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) contRowsSame provenanceContRowsSource
      provenanceContRowsRow
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary endpointSame
  exact And.intro
    (And.intro bundleUnary
      (And.intro vecspaceUnary
        (And.intro trivializationUnary
          (And.intro fibreUnary
            (And.intro transitionUnary'
              (And.intro overlapUnary
                (And.intro linearityUnary
                  (And.intro contRowsUnary'
                    (And.intro provenanceUnary
                      (And.intro endpointUnary'
                        (And.intro bundleVecspaceRow
                          (And.intro trivializationOverlapRow
                            (And.intro transitionLinearityRow
                              (And.intro provenanceContRowsRow pkgSig'))))))))))))))
    (And.intro contRowsSame endpointSame)

end BEDC.Derived.VectorBundleUp
