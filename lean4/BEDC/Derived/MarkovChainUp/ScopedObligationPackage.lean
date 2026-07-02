import BEDC.Derived.MarkovChainUp

namespace BEDC.Derived.MarkovChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MarkovChainTransitionCarrier_scoped_obligation_package [AskSetup] [PackageSetup]
    {prob random law transition controw provenance endpoint endpointPacked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      Cont endpoint provenance endpointPacked ->
        PkgSig bundle endpointPacked pkg ->
          MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
              bundle pkg ∧
            SemanticNameCert
              (fun row : BHist =>
                MarkovChainBHistTransitionCarrier prob random law transition controw provenance
                    endpoint bundle pkg ∧ hsame row endpointPacked)
              (fun row : BHist =>
                hsame row prob ∨ hsame row random ∨ hsame row law ∨ hsame row transition ∨
                  hsame row controw ∨ hsame row provenance ∨ hsame row endpoint ∨
                    hsame row endpointPacked)
              (fun _row : BHist =>
                MarkovChainBHistTransitionCarrier prob random law transition controw provenance
                    endpoint bundle pkg ∧
                  Cont endpoint provenance endpointPacked ∧ PkgSig bundle endpointPacked pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier packedCont packedPkg
  have sourcePattern : hsame endpointPacked prob ∨ hsame endpointPacked random ∨
      hsame endpointPacked law ∨ hsame endpointPacked transition ∨ hsame endpointPacked controw ∨
        hsame endpointPacked provenance ∨ hsame endpointPacked endpoint ∨
          hsame endpointPacked endpointPacked :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl endpointPacked)))))))
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
              bundle pkg ∧ hsame row endpointPacked)
        (fun row : BHist =>
          hsame row prob ∨ hsame row random ∨ hsame row law ∨ hsame row transition ∨
            hsame row controw ∨ hsame row provenance ∨ hsame row endpoint ∨
              hsame row endpointPacked)
        (fun row : BHist =>
          MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
              bundle pkg ∧
            Cont endpoint provenance endpointPacked ∧ PkgSig bundle endpointPacked pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointPacked (And.intro carrier (hsame_refl endpointPacked))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      cases source.right
      exact sourcePattern
    ledger_sound := by
      intro row source
      exact And.intro source.left (And.intro packedCont packedPkg)
  }
  exact And.intro carrier cert

end BEDC.Derived.MarkovChainUp
