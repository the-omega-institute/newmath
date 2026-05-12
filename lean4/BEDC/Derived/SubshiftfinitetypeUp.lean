import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubshiftfinitetypeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubshiftFiniteTypeCarrier [AskSetup] [PackageSetup]
    (alphabet word forbiddenLedger acceptanceLedger provenance localCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory alphabet ∧ UnaryHistory word ∧ UnaryHistory forbiddenLedger ∧
    UnaryHistory acceptanceLedger ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
      UnaryHistory endpoint ∧ Cont word forbiddenLedger acceptanceLedger ∧
        Cont alphabet word provenance ∧ Cont acceptanceLedger localCert endpoint ∧
          PkgSig bundle endpoint pkg

theorem SubshiftFiniteTypeCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {alphabet word forbiddenLedger acceptanceLedger provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubshiftFiniteTypeCarrier alphabet word forbiddenLedger acceptanceLedger provenance
        localCert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          SubshiftFiniteTypeCarrier alphabet word forbiddenLedger acceptanceLedger provenance
            localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          Cont word forbiddenLedger acceptanceLedger ∧ PkgSig bundle endpoint pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          Cont alphabet word provenance ∧ Cont acceptanceLedger localCert endpoint ∧
            hsame row endpoint)
        hsame := by
  intro carrier
  have carrierProof := carrier
  obtain ⟨_alphabetUnary, _wordUnary, _forbiddenLedgerUnary, _acceptanceLedgerUnary,
    _provenanceUnary, _localCertUnary, _endpointUnary, wordForbiddenAcceptance,
    alphabetWordProvenance, acceptanceLocalEndpoint, endpointPkg⟩ := carrier
  have endpointSource :
      (fun row : BHist =>
        SubshiftFiniteTypeCarrier alphabet word forbiddenLedger acceptanceLedger provenance
          localCert endpoint bundle pkg ∧ hsame row endpoint) endpoint := by
    exact ⟨carrierProof, hsame_refl endpoint⟩
  have core :
      NameCert
        (fun row : BHist =>
          SubshiftFiniteTypeCarrier alphabet word forbiddenLedger acceptanceLedger provenance
            localCert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := {
    carrier_inhabited := Exists.intro endpoint endpointSource
    equiv_refl := by
      intro row _source
      exact hsame_refl row
    equiv_symm := by
      intro row row' sameRows
      exact hsame_symm sameRows
    equiv_trans := by
      intro row row' row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    carrier_respects_equiv := by
      intro row row' sameRows source
      exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
  }
  exact {
    core := core
    pattern_sound := by
      intro row source
      exact ⟨wordForbiddenAcceptance, endpointPkg, source.right⟩
    ledger_sound := by
      intro row source
      exact ⟨alphabetWordProvenance, acceptanceLocalEndpoint, source.right⟩
  }

end BEDC.Derived.SubshiftfinitetypeUp
