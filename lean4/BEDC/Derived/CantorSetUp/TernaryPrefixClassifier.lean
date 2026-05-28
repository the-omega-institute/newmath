import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetCarrier_ternary_prefix_classifier [AskSetup] [PackageSetup]
    {T G I D prefixRead gapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory G →
        UnaryHistory I →
          UnaryHistory D →
            Cont T G prefixRead →
              Cont prefixRead I gapRead →
                PkgSig bundle T pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row prefixRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row T ∨ hsame row G ∨ hsame row prefixRead ∨ hsame row I)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont T G prefixRead ∧
                          Cont prefixRead I gapRead ∧ PkgSig bundle T pkg)
                      hsame ∧
                    UnaryHistory prefixRead ∧ UnaryHistory gapRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro prefixUnary gapUnary intervalUnary _deletedUnary prefixRoute gapRoute prefixPkg
  have prefixReadUnary : UnaryHistory prefixRead :=
    unary_cont_closed prefixUnary gapUnary prefixRoute
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed prefixReadUnary intervalUnary gapRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row prefixRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row prefixRead ∨ hsame row I)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T G prefixRead ∧
              Cont prefixRead I gapRead ∧ PkgSig bundle T pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro prefixRead ⟨hsame_refl prefixRead, prefixReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, prefixRoute, gapRoute, prefixPkg⟩
  }
  exact ⟨cert, prefixReadUnary, gapReadUnary⟩

end BEDC.Derived.CantorSetUp
