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

theorem CstaralgebraBHistCarrier_unital_commutative_source_boundary [AskSetup] [PackageSetup]
    {banach ring mul involution normSquare carrierTransport multiplicationTransport
      involutionTransport normTransport provenance ledger endpoint unit commutativity : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CstaralgebraBHistCarrier banach ring mul involution normSquare carrierTransport
        multiplicationTransport involutionTransport normTransport provenance ledger endpoint
        bundle pkg ->
      UnaryHistory unit ->
        UnaryHistory commutativity ->
          Cont unit commutativity ledger ->
            UnaryHistory banach ∧ UnaryHistory ring ∧ UnaryHistory mul ∧
              UnaryHistory unit ∧ UnaryHistory commutativity ∧ UnaryHistory involution ∧
                UnaryHistory normSquare ∧ Cont unit commutativity ledger ∧
                  hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro carrier unitUnary commutativityUnary unitCommutativityLedger
  have banachUnary : UnaryHistory banach :=
    carrier.left
  have ringUnary : UnaryHistory ring :=
    carrier.right.left
  have mulUnary : UnaryHistory mul :=
    carrier.right.right.left
  have involutionUnary : UnaryHistory involution :=
    carrier.right.right.right.left
  have normSquareUnary : UnaryHistory normSquare :=
    carrier.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.left
  have ledgerEndpoint : Cont ledger provenance endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed unitUnary commutativityUnary unitCommutativityLedger
  have endpointReadback : hsame endpoint (append provenance ledger) :=
    hsame_trans ledgerEndpoint (unary_append_comm_hsame ledgerUnary provenanceUnary)
  exact And.intro banachUnary
    (And.intro ringUnary
      (And.intro mulUnary
        (And.intro unitUnary
          (And.intro commutativityUnary
            (And.intro involutionUnary
              (And.intro normSquareUnary
                (And.intro unitCommutativityLedger
                  (And.intro endpointReadback pkgSig))))))))

end BEDC.Derived.CstaralgebraUp
