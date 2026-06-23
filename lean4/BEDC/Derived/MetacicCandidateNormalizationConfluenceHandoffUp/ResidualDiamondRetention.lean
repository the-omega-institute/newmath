import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateHandoffResidualDiamondRetention [AskSetup] [PackageSetup]
    {A K N F C D B T R P L candidateRead frontierRead confluenceRead decidableRead
      blockedRead residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P L bundle pkg →
      Cont A K candidateRead →
        Cont candidateRead F frontierRead →
          Cont frontierRead C confluenceRead →
            Cont confluenceRead D decidableRead →
              Cont decidableRead B blockedRead →
                Cont blockedRead R residualRead →
                  PkgSig bundle residualRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row K ∨ hsame row C ∨ hsame row D ∨ hsame row B ∨
                            hsame row residualRead)
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle residualRead pkg)
                        hsame ∧
                      UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                        UnaryHistory confluenceRead ∧ UnaryHistory decidableRead ∧
                          UnaryHistory blockedRead ∧ UnaryHistory residualRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier candidateRoute frontierRoute confluenceRoute decidableRoute blockedRoute
    residualRoute residualPkg
  have auditUnary : UnaryHistory A := carrier.left
  have candidateUnary : UnaryHistory K := carrier.right.left
  have frontierUnary : UnaryHistory F := carrier.right.right.right.left
  have confluenceUnary : UnaryHistory C := carrier.right.right.right.right.left
  have decidableUnary : UnaryHistory D := carrier.right.right.right.right.right.left
  have blockedUnary : UnaryHistory B := carrier.right.right.right.right.right.right.left
  have residualUnary : UnaryHistory R :=
    carrier.right.right.right.right.right.right.right.right.left
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
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed blockedReadUnary residualUnary residualRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row C ∨ hsame row D ∨ hsame row B ∨
              hsame row residualRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle residualRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead
        ⟨hsame_refl residualRead, residualReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, residualPkg⟩
  }
  exact
    ⟨cert, candidateReadUnary, frontierReadUnary, confluenceReadUnary, decidableReadUnary,
      blockedReadUnary, residualReadUnary⟩

end BEDC.Derived
