import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VectorBundleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

def VectorBundleComponentwiseClassifier [AskSetup] [PackageSetup]
    (bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance endpoint
      bundleRow' vecspace' trivialization' fibre' transition' overlap' linearity' contRows'
      provenance' endpoint' : BHist) : Prop :=
  UnaryHistory bundleRow ∧ UnaryHistory vecspace ∧ UnaryHistory fibre ∧
    UnaryHistory transition ∧ UnaryHistory overlap ∧ UnaryHistory linearity ∧
      UnaryHistory contRows ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        UnaryHistory bundleRow' ∧ UnaryHistory vecspace' ∧ UnaryHistory fibre' ∧
          UnaryHistory transition' ∧ UnaryHistory overlap' ∧ UnaryHistory linearity' ∧
            UnaryHistory contRows' ∧ UnaryHistory provenance' ∧ UnaryHistory endpoint' ∧
              hsame bundleRow bundleRow' ∧ hsame vecspace vecspace' ∧
                hsame fibre fibre' ∧ hsame overlap overlap' ∧ hsame linearity linearity' ∧
                  hsame provenance provenance' ∧ Cont bundleRow vecspace trivialization ∧
                    Cont bundleRow' vecspace' trivialization' ∧
                      Cont trivialization overlap transition ∧
                        Cont trivialization' overlap' transition' ∧
                          Cont transition linearity contRows ∧
                            Cont transition' linearity' contRows' ∧
                              Cont provenance contRows endpoint ∧
                                Cont provenance' contRows' endpoint'

def VectorBundleFiniteClassifier [AskSetup] [PackageSetup]
    (bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance
      endpoint bundleRow' vecspace' trivialization' fibre' transition' overlap' linearity'
      contRows' provenance' endpoint' : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
      linearity contRows provenance endpoint probe pkg ∧
    VectorBundleFiniteCarrier bundleRow' vecspace' trivialization' fibre' transition' overlap'
      linearity' contRows' provenance' endpoint' probe pkg ∧
      hsame bundleRow bundleRow' ∧ hsame vecspace vecspace' ∧ hsame fibre fibre' ∧
        hsame overlap overlap' ∧ hsame linearity linearity' ∧ hsame contRows contRows' ∧
          hsame endpoint endpoint'

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

theorem VectorBundleFiniteCarrier_carrier_obligation [AskSetup] [PackageSetup]
    {bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance
      endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap linearity
        contRows provenance endpoint probe pkg ->
      UnaryHistory bundleRow ∧ UnaryHistory vecspace ∧ UnaryHistory trivialization ∧
        UnaryHistory fibre ∧ UnaryHistory transition ∧ UnaryHistory endpoint ∧
          Cont bundleRow vecspace trivialization ∧ Cont trivialization overlap transition ∧
            Cont transition linearity contRows ∧ Cont provenance contRows endpoint ∧
              PkgSig probe endpoint pkg := by
  intro carrier
  obtain ⟨bundleUnary, vecspaceUnary, trivializationUnary, fibreUnary, transitionUnary,
    _overlapUnary, _linearityUnary, _contRowsUnary, _provenanceUnary, endpointUnary,
    bundleVecspaceRow, trivializationOverlapRow, transitionLinearityRow,
    provenanceContRowsRow, pkgSig⟩ := carrier
  exact
    ⟨bundleUnary, vecspaceUnary, trivializationUnary, fibreUnary, transitionUnary,
      endpointUnary, bundleVecspaceRow, trivializationOverlapRow, transitionLinearityRow,
      provenanceContRowsRow, pkgSig⟩

def VectorBundleFiniteCarrierClassifier [AskSetup] [PackageSetup]
    (bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance
      endpoint bundleRow' vecspace' trivialization' fibre' transition' overlap' linearity'
      contRows' provenance' endpoint' : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap linearity
      contRows provenance endpoint probe pkg ∧
    VectorBundleFiniteCarrier bundleRow' vecspace' trivialization' fibre' transition' overlap'
      linearity' contRows' provenance' endpoint' probe pkg ∧
      hsame bundleRow bundleRow' ∧ hsame vecspace vecspace' ∧ hsame fibre fibre' ∧
        hsame overlap overlap' ∧ hsame linearity linearity' ∧ hsame endpoint endpoint'

theorem VectorBundleFiniteCarrierClassifier_transport [AskSetup] [PackageSetup]
    {bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance
      endpoint bundleRow' vecspace' trivialization' fibre' transition' overlap' linearity'
      contRows' provenance' endpoint' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    VectorBundleFiniteCarrierClassifier bundleRow vecspace trivialization fibre transition overlap
        linearity contRows provenance endpoint bundleRow' vecspace' trivialization' fibre'
        transition' overlap' linearity' contRows' provenance' endpoint' probe pkg ->
      VectorBundleFiniteCarrier bundleRow' vecspace' trivialization' fibre' transition' overlap'
          linearity' contRows' provenance' endpoint' probe pkg ∧
        hsame endpoint endpoint' := by
  intro classifier
  exact And.intro classifier.right.left classifier.right.right.right.right.right.right.right

theorem VectorBundleFiniteCarrier_obligation_surface [AskSetup] [PackageSetup]
    {bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance
      endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
        linearity contRows provenance endpoint probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition
                overlap linearity contRows provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition
                overlap linearity contRows provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition
                overlap linearity contRows provenance e probe pkg ∧ hsame row e)
          hsame ∧
        Cont bundleRow vecspace trivialization ∧ Cont trivialization overlap transition ∧
          Cont transition linearity contRows ∧ Cont provenance contRows endpoint ∧
            PkgSig probe endpoint pkg := by
  intro carrierData
  have endpointCarrier :
      VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
        linearity contRows provenance endpoint probe pkg :=
    carrierData
  obtain ⟨_bundleUnary, _vecspaceUnary, _trivializationUnary, _fibreUnary,
    _transitionUnary, _overlapUnary, _linearityUnary, _contRowsUnary, _provenanceUnary,
    _endpointUnary, bundleRowData, transitionRow, contRowsRow, endpointRow,
    packageRow⟩ := carrierData
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition
            overlap linearity contRows provenance e probe pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro endpointCarrier (hsame_refl endpoint))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition
                overlap linearity contRows provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition
                overlap linearity contRows provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition
                overlap linearity contRows provenance e probe pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        cases sourceRow with
        | intro e endpointData =>
            exact Exists.intro e
              (And.intro endpointData.left
                (hsame_trans (hsame_symm sameRows) endpointData.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro bundleRowData
      (And.intro transitionRow (And.intro contRowsRow (And.intro endpointRow packageRow))))

theorem VectorBundleFiniteCarrier_transition_composition_scope [AskSetup] [PackageSetup]
    {bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance
      endpoint composed : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap linearity
        contRows provenance endpoint probe pkg ->
      Cont contRows transition composed ->
        UnaryHistory composed ∧ Cont bundleRow vecspace trivialization ∧
          Cont trivialization overlap transition ∧ Cont transition linearity contRows ∧
            Cont contRows transition composed ∧ PkgSig probe endpoint pkg := by
  intro carrier composedRow
  obtain ⟨_bundleUnary, _vecspaceUnary, _trivializationUnary, _fibreUnary,
    transitionUnary, _overlapUnary, _linearityUnary, contRowsUnary, _provenanceUnary,
    _endpointUnary, bundleVecspaceRow, trivializationOverlapRow, transitionLinearityRow,
    _provenanceContRowsRow, pkgSig⟩ := carrier
  have composedUnary : UnaryHistory composed :=
    unary_cont_closed contRowsUnary transitionUnary composedRow
  exact And.intro composedUnary
    (And.intro bundleVecspaceRow
      (And.intro trivializationOverlapRow
        (And.intro transitionLinearityRow
          (And.intro composedRow pkgSig))))

end BEDC.Derived.VectorBundleUp
