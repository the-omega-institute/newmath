import BEDC.Derived.ContourSumWindowUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContourSumWindowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContourSumWindowCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {contour holomorphic subdivision riemann output transport continuation provenance name
      ledgerRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory contour →
      UnaryHistory holomorphic →
        UnaryHistory subdivision →
          UnaryHistory riemann →
            UnaryHistory output →
              Cont contour holomorphic subdivision →
                Cont subdivision riemann ledgerRead →
                  Cont ledgerRead output outputRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle outputRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              (hsame row ledgerRead ∨ hsame row outputRead) ∧
                                UnaryHistory row)
                            (fun row : BHist =>
                              hsame row contour ∨ hsame row holomorphic ∨
                                hsame row subdivision ∨ hsame row riemann ∨
                                  hsame row output ∨ hsame row ledgerRead ∨
                                    hsame row outputRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle outputRead pkg)
                            hsame ∧
                          UnaryHistory ledgerRead ∧ UnaryHistory outputRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _contourUnary _holomorphicUnary subdivisionUnary riemannUnary outputUnary
    _subdivisionRoute ledgerRoute outputRoute provenancePkg outputPkg
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed subdivisionUnary riemannUnary ledgerRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed ledgerUnary outputUnary outputRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row ledgerRead ∨ hsame row outputRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row contour ∨ hsame row holomorphic ∨ hsame row subdivision ∨
              hsame row riemann ∨ hsame row output ∨ hsame row ledgerRead ∨
                hsame row outputRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle outputRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro outputRead ⟨Or.inr (hsame_refl outputRead),
          outputReadUnary⟩
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
          · cases source.left with
            | inl sameLedger =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameLedger)
            | inr sameOutput =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameOutput)
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameLedger =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameLedger)))))
        | inr sameOutput =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameOutput)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, outputPkg⟩
  }
  exact ⟨cert, ledgerUnary, outputReadUnary⟩

end BEDC.Derived.ContourSumWindowUp
