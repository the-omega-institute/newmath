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

theorem VectorBundleFiniteCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {bundleRow vecspace trivialization fibre transition overlap linearity contRows provenance
      endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
        linearity contRows provenance endpoint probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
              linearity contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
              linearity contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
              linearity contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          hsame ∧
        Cont bundleRow vecspace trivialization ∧ Cont trivialization overlap transition ∧
          Cont transition linearity contRows ∧ Cont provenance contRows endpoint ∧
            PkgSig probe endpoint pkg := by
  intro carrier
  have carrierData := carrier
  obtain ⟨_bundleUnary, _vecspaceUnary, _trivializationUnary, _fibreUnary,
    _transitionUnary, _overlapUnary, _linearityUnary, _contRowsUnary, _provenanceUnary,
    _endpointUnary, bundleVecspaceRow, trivializationOverlapRow, transitionLinearityRow,
    provenanceContRowsRow, pkgSig⟩ := carrier
  have endpointSource :
      (fun row : BHist =>
        VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
          linearity contRows provenance endpoint probe pkg ∧ hsame row endpoint) endpoint :=
    And.intro carrierData (hsame_refl endpoint)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
              linearity contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
              linearity contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            VectorBundleFiniteCarrier bundleRow vecspace trivialization fibre transition overlap
              linearity contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro bundleVecspaceRow
      (And.intro trivializationOverlapRow
        (And.intro transitionLinearityRow (And.intro provenanceContRowsRow pkgSig))))

end BEDC.Derived.VectorBundleUp
