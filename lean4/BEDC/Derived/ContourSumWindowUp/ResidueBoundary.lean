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

theorem ContourSumWindow_residue_boundary [AskSetup] [PackageSetup]
    {contour holomorphic subdivision riemann output transport continuation provenance name
      ledgerRead outputRead residueRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory contour ->
      UnaryHistory holomorphic ->
        UnaryHistory subdivision ->
          UnaryHistory riemann ->
            UnaryHistory output ->
              UnaryHistory continuation ->
                Cont contour holomorphic subdivision ->
                  Cont subdivision riemann ledgerRead ->
                    Cont ledgerRead output outputRead ->
                      Cont output continuation residueRead ->
                        PkgSig bundle provenance pkg ->
                          PkgSig bundle outputRead pkg ->
                            SemanticNameCert
                                (fun row : BHist =>
                                  (hsame row outputRead ∨ hsame row residueRead) ∧
                                    UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row contour ∨ hsame row holomorphic ∨
                                    hsame row subdivision ∨ hsame row riemann ∨
                                      hsame row output ∨ hsame row continuation ∨
                                        hsame row outputRead ∨ hsame row residueRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle outputRead pkg)
                                hsame ∧
                              UnaryHistory residueRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _contourUnary _holomorphicUnary subdivisionUnary riemannUnary outputUnary
    continuationUnary _subdivisionRoute ledgerRoute outputRoute residueRoute provenancePkg
    outputPkg
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed subdivisionUnary riemannUnary ledgerRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed ledgerUnary outputUnary outputRoute
  have residueUnary : UnaryHistory residueRead :=
    unary_cont_closed outputUnary continuationUnary residueRoute
  have sourceAtResidue :
      (fun row : BHist =>
        (hsame row outputRead ∨ hsame row residueRead) ∧ UnaryHistory row) residueRead :=
    ⟨Or.inr (hsame_refl residueRead), residueUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row outputRead ∨ hsame row residueRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row contour ∨ hsame row holomorphic ∨ hsame row subdivision ∨
              hsame row riemann ∨ hsame row output ∨ hsame row continuation ∨
                hsame row outputRead ∨ hsame row residueRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle outputRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residueRead sourceAtResidue
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
          | inl sameOutput =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameOutput)
          | inr sameResidue =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameResidue)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameOutput =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameOutput))))))
      | inr sameResidue =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameResidue))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, outputPkg⟩
  }
  exact ⟨cert, residueUnary⟩

end BEDC.Derived.ContourSumWindowUp
