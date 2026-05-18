import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row provenance ∧
            DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        (fun row : BHist =>
          hsame row provenance ∧ Cont window ledger provenance ∧
            PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  rcases carrier with
    ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
      precisionEndpointWindow, windowLedgerProvenance, pkgSig⟩
  constructor
  · constructor
    · exact
        ⟨provenance,
          And.intro (hsame_refl provenance)
            ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
              precisionEndpointWindow, windowLedgerProvenance, pkgSig⟩⟩
    · intro row _source
      exact hsame_refl row
    · intro row row' sameRow
      exact hsame_symm sameRow
    · intro row row' row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro row row' sameRow source
      have sameRowProvenance : hsame row provenance := source.left
      exact
        And.intro (hsame_trans (hsame_symm sameRow) sameRowProvenance) source.right
  · intro row source
    have rowUnary : UnaryHistory row :=
      unary_transport_symm provenanceUnary source.left
    exact And.intro rowUnary pkgSig
  · intro row source
    exact And.intro source.left (And.intro windowLedgerProvenance pkgSig)

end BEDC.Derived.DyadicApproximationUp
