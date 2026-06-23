import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffNormalEndpointReadback
    [AskSetup] [PackageSetup]
    {A K N F C D B T R P L candidateRead frontierRead confluenceRead decidableRead
      blockedRead endpointRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P L bundle pkg →
      Cont A K candidateRead →
        Cont candidateRead F frontierRead →
          Cont frontierRead C confluenceRead →
            Cont confluenceRead D decidableRead →
              Cont decidableRead B blockedRead →
                Cont blockedRead N endpointRead →
                  Cont endpointRead L namedRead →
                    PkgSig bundle namedRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row K ∨ hsame row F ∨ hsame row C ∨ hsame row D ∨
                              hsame row B ∨ hsame row N ∨ hsame row namedRead)
                          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle namedRead pkg)
                          hsame ∧
                        UnaryHistory endpointRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier candidateRoute frontierRoute confluenceRoute decidableRoute blockedRoute
    endpointRoute namedRoute namedPkg
  have auditUnary : UnaryHistory A := carrier.left
  have candidateUnary : UnaryHistory K := carrier.right.left
  have endpointUnary : UnaryHistory N := carrier.right.right.left
  have frontierUnary : UnaryHistory F := carrier.right.right.right.left
  have confluenceUnary : UnaryHistory C := carrier.right.right.right.right.left
  have decidableUnary : UnaryHistory D := carrier.right.right.right.right.right.left
  have blockedUnary : UnaryHistory B := carrier.right.right.right.right.right.right.left
  have localNameUnary : UnaryHistory L :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed auditUnary candidateUnary candidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateReadUnary frontierUnary frontierRoute
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed frontierReadUnary confluenceUnary confluenceRoute
  have decidableReadUnary : UnaryHistory decidableRead :=
    unary_cont_closed confluenceReadUnary decidableUnary decidableRoute
  have blockedReadUnary : UnaryHistory blockedRead :=
    unary_cont_closed decidableReadUnary blockedUnary blockedRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed blockedReadUnary endpointUnary endpointRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed endpointReadUnary localNameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row C ∨ hsame row D ∨
              hsame row B ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namedPkg⟩
  }
  exact ⟨cert, endpointReadUnary, namedReadUnary⟩

end BEDC.Derived
