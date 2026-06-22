import BEDC.Derived.ContourSumWindowUp.SubdivisionExactness

namespace BEDC.Derived.ContourSumWindowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContourSumWindowCarrier_refinement_stability [AskSetup] [PackageSetup]
    {subdivision riemann output ledgerRead outputRead continuation refinedRead provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory subdivision →
      UnaryHistory riemann →
        UnaryHistory output →
          UnaryHistory continuation →
            Cont subdivision riemann ledgerRead →
              Cont ledgerRead output outputRead →
                Cont outputRead continuation refinedRead →
                  PkgSig bundle provenance pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row subdivision ∨ hsame row riemann ∨ hsame row outputRead ∨
                            hsame row refinedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont subdivision riemann ledgerRead ∧
                            Cont ledgerRead output outputRead ∧
                              Cont outputRead continuation refinedRead ∧
                                PkgSig bundle provenance pkg)
                        hsame ∧
                      UnaryHistory refinedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro subdivisionUnary riemannUnary outputUnary continuationUnary ledgerRoute outputRoute
    refinementRoute provenancePkg
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed subdivisionUnary riemannUnary ledgerRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed ledgerUnary outputUnary outputRoute
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed outputReadUnary continuationUnary refinementRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row subdivision ∨ hsame row riemann ∨ hsame row outputRead ∨
              hsame row refinedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont subdivision riemann ledgerRead ∧
              Cont ledgerRead output outputRead ∧ Cont outputRead continuation refinedRead ∧
                PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro refinedRead ⟨hsame_refl refinedRead, refinedUnary⟩
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
          constructor
          · exact hsame_trans (hsame_symm sameRows) source.left
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, ledgerRoute, outputRoute, refinementRoute, provenancePkg⟩
    }
  exact ⟨cert, refinedUnary⟩

end BEDC.Derived.ContourSumWindowUp
