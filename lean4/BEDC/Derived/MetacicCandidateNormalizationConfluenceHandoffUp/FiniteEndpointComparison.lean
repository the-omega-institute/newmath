import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffFiniteEndpointComparison
    [AskSetup] [PackageSetup]
    {A K N F C D B T R P L candidateRead frontierRead endpointRead comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P L bundle pkg ->
      Cont A K candidateRead ->
        Cont candidateRead F frontierRead ->
          Cont frontierRead N endpointRead ->
            Cont endpointRead D comparisonRead ->
              PkgSig bundle comparisonRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row F ∨ hsame row C ∨ hsame row D ∨
                        hsame row B ∨ hsame row comparisonRead)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle comparisonRead pkg)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                    UnaryHistory endpointRead ∧ UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier candidateRoute frontierRoute endpointRoute comparisonRoute comparisonPkg
  have auditUnary : UnaryHistory A := carrier.left
  have candidateUnary : UnaryHistory K := carrier.right.left
  have endpointUnary : UnaryHistory N := carrier.right.right.left
  have frontierUnary : UnaryHistory F := carrier.right.right.right.left
  have decidableUnary : UnaryHistory D := carrier.right.right.right.right.right.left
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed auditUnary candidateUnary candidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateReadUnary frontierUnary frontierRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed frontierReadUnary endpointUnary endpointRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed endpointReadUnary decidableUnary comparisonRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row C ∨ hsame row D ∨
              hsame row B ∨ hsame row comparisonRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle comparisonRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro comparisonRead ⟨hsame_refl comparisonRead, comparisonReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, comparisonPkg⟩
  }
  exact
    ⟨cert, candidateReadUnary, frontierReadUnary, endpointReadUnary,
      comparisonReadUnary⟩

end BEDC.Derived
