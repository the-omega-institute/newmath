import BEDC.Derived.FiniteKernelCategoryUp.Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FiniteKernelCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteKernelCategoryNamecertObligations [AskSetup] [PackageSetup]
    {objectRow homRow identityRow compositionRow associativityRow unitRow transportRow
      routeRow provenanceRow nameCertRow objectRead homRead compositeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory objectRow →
      UnaryHistory homRow →
        UnaryHistory identityRow →
          UnaryHistory compositionRow →
            UnaryHistory associativityRow →
              UnaryHistory unitRow →
                UnaryHistory transportRow →
                  UnaryHistory routeRow →
                    UnaryHistory provenanceRow →
                      UnaryHistory nameCertRow →
                        Cont objectRow homRow homRead →
                          Cont homRead compositionRow compositeRead →
                            hsame transportRow nameCertRow →
                              PkgSig bundle provenanceRow pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row nameCertRow ∧
                                      UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row objectRow ∨ hsame row homRow ∨
                                        hsame row identityRow ∨ hsame row compositionRow ∨
                                          hsame row nameCertRow)
                                    (fun row : BHist =>
                                      hsame row nameCertRow ∧
                                        PkgSig bundle provenanceRow pkg)
                                    hsame ∧
                                  Cont objectRow homRow homRead ∧
                                    Cont homRead compositionRow compositeRead ∧
                                      hsame transportRow nameCertRow ∧
                                        PkgSig bundle provenanceRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro objectUnary homUnary identityUnary compositionUnary _associativityUnary _unitUnary
    _transportUnary _routeUnary _provenanceUnary nameCertUnary objectRoute compositeRoute
    transportSame provenancePkg
  have sourceNameCert :
      (fun row : BHist => hsame row nameCertRow ∧ UnaryHistory row) nameCertRow := by
    exact ⟨hsame_refl nameCertRow, nameCertUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameCertRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row objectRow ∨ hsame row homRow ∨ hsame row identityRow ∨
              hsame row compositionRow ∨ hsame row nameCertRow)
          (fun row : BHist => hsame row nameCertRow ∧ PkgSig bundle provenanceRow pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameCertRow sourceNameCert
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
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, objectRoute, compositeRoute, transportSame, provenancePkg⟩

end BEDC.Derived.FiniteKernelCategoryUp
