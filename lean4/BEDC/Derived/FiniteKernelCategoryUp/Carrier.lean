import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.FiniteKernelCategoryUp.TasteGate

namespace BEDC.Derived.FiniteKernelCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteKernelCategoryCarrier_object_hom_boundary [AskSetup] [PackageSetup]
    {objectRow homRow identityRow compositionRow associativityRow unitRow transportRow
      routeRow provenanceRow nameCertRow objectRead homRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory objectRow →
      UnaryHistory homRow →
        Cont objectRow homRow homRead →
          PkgSig bundle objectRead pkg →
            PkgSig bundle homRead pkg →
              (∃ packet : FiniteKernelCategoryUp,
                packet =
                  FiniteKernelCategoryUp.mk objectRow homRow identityRow compositionRow
                    associativityRow unitRow transportRow routeRow provenanceRow nameCertRow) ∧
                UnaryHistory objectRow ∧ UnaryHistory homRow ∧
                  Cont objectRow homRow homRead ∧ PkgSig bundle objectRead pkg ∧
                    PkgSig bundle homRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro objectUnary homUnary homRoute objectPkg homPkg
  exact
    ⟨Exists.intro
      (FiniteKernelCategoryUp.mk objectRow homRow identityRow compositionRow associativityRow
        unitRow transportRow routeRow provenanceRow nameCertRow) rfl,
      objectUnary, homUnary, homRoute, objectPkg, homPkg⟩

theorem FiniteKernelCategoryLedgerNonescapeBoundary [AskSetup] [PackageSetup]
    {objectRow homRow identityRow compositionRow associativityRow unitRow transportRow
      routeRow provenanceRow nameCertRow ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory objectRow →
      UnaryHistory homRow →
        UnaryHistory identityRow →
          UnaryHistory compositionRow →
            UnaryHistory associativityRow →
              UnaryHistory unitRow →
                UnaryHistory routeRow →
                  UnaryHistory provenanceRow →
                    UnaryHistory nameCertRow →
                      Cont routeRow nameCertRow ledgerRead →
                        PkgSig bundle provenanceRow pkg →
                          PkgSig bundle ledgerRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row objectRow ∨ hsame row homRow ∨
                                    hsame row identityRow ∨ hsame row compositionRow ∨
                                      hsame row associativityRow ∨ hsame row unitRow ∨
                                        hsame row ledgerRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle provenanceRow pkg ∧
                                    PkgSig bundle ledgerRead pkg)
                                hsame ∧
                              UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro _objectUnary _homUnary _identityUnary _compositionUnary _associativityUnary _unitUnary
    routeUnary _provenanceUnary nameCertUnary ledgerRoute provenancePkg ledgerPkg
  have _transportRowTouch : BHist := transportRow
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed routeUnary nameCertUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row objectRow ∨ hsame row homRow ∨ hsame row identityRow ∨
              hsame row compositionRow ∨ hsame row associativityRow ∨ hsame row unitRow ∨
                hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenanceRow pkg ∧ PkgSig bundle ledgerRead pkg)
          hsame := by
    refine
      { core :=
          { carrier_inhabited := ?_
            equiv_refl := ?_
            equiv_symm := ?_
            equiv_trans := ?_
            carrier_respects_equiv := ?_ }
        pattern_sound := ?_
        ledger_sound := ?_ }
    · exact ⟨ledgerRead, hsame_refl ledgerRead, ledgerUnary⟩
    · intro row _source
      exact hsame_refl row
    · intro row other same
      exact hsame_symm same
    · intro row middle other leftSame rightSame
      exact hsame_trans leftSame rightSame
    · intro row other same source
      exact
        ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    · intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    · intro row source
      exact ⟨source.right, provenancePkg, ledgerPkg⟩
  exact ⟨cert, ledgerUnary⟩

end BEDC.Derived.FiniteKernelCategoryUp
