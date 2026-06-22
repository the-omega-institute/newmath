import BEDC.Derived.ContourSumWindowUp.NameCertObligations

namespace BEDC.Derived.ContourSumWindowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContourSumWindowCarrier_subdivision_exactness [AskSetup] [PackageSetup]
    {subdivision riemann ledgerRead provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory subdivision →
      UnaryHistory riemann →
        Cont subdivision riemann ledgerRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle ledgerRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row subdivision ∨ hsame row riemann ∨ hsame row ledgerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont subdivision riemann ledgerRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg)
                  hsame ∧
                UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro subdivisionUnary riemannUnary ledgerRoute provenancePkg ledgerPkg
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed subdivisionUnary riemannUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row subdivision ∨ hsame row riemann ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont subdivision riemann ledgerRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨source.right, ledgerRoute, provenancePkg, ledgerPkg⟩
    }
  exact ⟨cert, ledgerUnary⟩

end BEDC.Derived.ContourSumWindowUp
