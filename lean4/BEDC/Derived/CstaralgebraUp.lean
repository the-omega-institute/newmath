import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CstaralgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CstaralgebraBHistCarrier [AskSetup] [PackageSetup]
    (banach ring mul involution normSquare carrierTransport multiplicationTransport
      involutionTransport normTransport provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory banach ∧ UnaryHistory ring ∧ UnaryHistory mul ∧ UnaryHistory involution ∧
    UnaryHistory normSquare ∧ UnaryHistory provenance ∧ hsame carrierTransport banach ∧
      hsame multiplicationTransport mul ∧ hsame involutionTransport involution ∧
        hsame normTransport normSquare ∧ Cont mul involution ledger ∧
          Cont ledger provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem CstaralgebraNameCert_obligation_surface [AskSetup] [PackageSetup]
    {banach ring mul involution normSquare carrierTransport multiplicationTransport
      involutionTransport normTransport provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CstaralgebraBHistCarrier banach ring mul involution normSquare carrierTransport
        multiplicationTransport involutionTransport normTransport provenance ledger endpoint
        bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame ∧
        UnaryHistory banach ∧ UnaryHistory ring ∧ UnaryHistory involution ∧
          UnaryHistory normSquare ∧ Cont mul involution ledger ∧
            Cont ledger provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have unaryBanach : UnaryHistory banach :=
    carrier.left
  have unaryRing : UnaryHistory ring :=
    carrier.right.left
  have unaryInvolution : UnaryHistory involution :=
    carrier.right.right.right.left
  have unaryNormSquare : UnaryHistory normSquare :=
    carrier.right.right.right.right.left
  have mulInvolutionLedger : Cont mul involution ledger :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have ledgerEndpoint : Cont ledger provenance endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        exact hsame_trans (hsame_symm sameRows) carrierRow
    }
    pattern_sound := by
      intro _row carrierRow
      exact carrierRow
    ledger_sound := by
      intro _row carrierRow
      exact carrierRow
  }
  exact And.intro cert
    (And.intro unaryBanach
      (And.intro unaryRing
        (And.intro unaryInvolution
          (And.intro unaryNormSquare
            (And.intro mulInvolutionLedger
              (And.intro ledgerEndpoint pkgSig))))))

theorem CstaralgebraBHistCarrier_classifier_stability [AskSetup] [PackageSetup]
    {banach ring mul involution normSquare carrierTransport multiplicationTransport
      involutionTransport normTransport provenance ledger endpoint banach' ring' mul' involution'
      normSquare' provenance' ledger' endpoint' : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    CstaralgebraBHistCarrier banach ring mul involution normSquare carrierTransport
        multiplicationTransport involutionTransport normTransport provenance ledger endpoint bundle pkg ->
      hsame banach banach' -> hsame ring ring' -> hsame mul mul' ->
        hsame involution involution' -> hsame normSquare normSquare' ->
          hsame provenance provenance' ->
            Cont mul' involution' ledger' -> Cont ledger' provenance' endpoint' ->
              PkgSig bundle endpoint' pkg ->
                CstaralgebraBHistCarrier banach' ring' mul' involution' normSquare'
                    carrierTransport multiplicationTransport involutionTransport normTransport
                    provenance' ledger' endpoint' bundle pkg ∧ hsame ledger ledger' ∧
                  hsame endpoint endpoint' := by
  intro carrier sameBanach sameRing sameMul sameInvolution sameNormSquare sameProvenance
    ledgerCont' endpointCont' pkgSig'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameMul sameInvolution
      carrier.right.right.right.right.right.right.right.right.right.right.left ledgerCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger sameProvenance
      carrier.right.right.right.right.right.right.right.right.right.right.right.left endpointCont'
  have transported :
      CstaralgebraBHistCarrier banach' ring' mul' involution' normSquare'
          carrierTransport multiplicationTransport involutionTransport normTransport
          provenance' ledger' endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameBanach,
      unary_transport carrier.right.left sameRing,
      unary_transport carrier.right.right.left sameMul,
      unary_transport carrier.right.right.right.left sameInvolution,
      unary_transport carrier.right.right.right.right.left sameNormSquare,
      unary_transport carrier.right.right.right.right.right.left sameProvenance,
      hsame_trans carrier.right.right.right.right.right.right.left sameBanach,
      hsame_trans carrier.right.right.right.right.right.right.right.left sameMul,
      hsame_trans carrier.right.right.right.right.right.right.right.right.left sameInvolution,
      hsame_trans carrier.right.right.right.right.right.right.right.right.right.left
        sameNormSquare,
      ledgerCont',
      endpointCont',
      pkgSig'⟩
  exact And.intro transported (And.intro sameLedger sameEndpoint)

end BEDC.Derived.CstaralgebraUp
