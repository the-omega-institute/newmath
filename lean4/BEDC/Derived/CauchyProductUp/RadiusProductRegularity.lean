import BEDC.Derived.CauchyProductUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_radius_product_regularity [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name radiusLedger budgetRead regseqSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont radiusA radiusB radiusLedger ->
        Cont radiusLedger product budgetRead ->
          Cont budgetRead classifier regseqSeal ->
            PkgSig bundle regseqSeal pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row radiusLedger ∨ hsame row budgetRead ∨
                      hsame row regseqSeal ∨ hsame row product)
                  (fun row : BHist =>
                    hsame row radiusLedger ∨ hsame row budgetRead ∨
                      hsame row regseqSeal ∨ hsame row product)
                  (fun row : BHist =>
                    PkgSig bundle regseqSeal pkg ∧
                      (hsame row radiusLedger ∨ hsame row budgetRead ∨
                        hsame row regseqSeal ∨ hsame row product))
                  hsame ∧
                UnaryHistory radiusA ∧ UnaryHistory radiusB ∧ UnaryHistory radiusLedger ∧
                  UnaryHistory product ∧ UnaryHistory budgetRead ∧ UnaryHistory regseqSeal ∧
                    Cont radiusA radiusB radiusLedger ∧
                      Cont radiusLedger product budgetRead ∧
                        Cont budgetRead classifier regseqSeal ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle regseqSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet radiusRoute budgetRoute regseqRoute regseqPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have radiusLedgerUnary : UnaryHistory radiusLedger :=
    unary_cont_closed radiusAUnary radiusBUnary radiusRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed radiusLedgerUnary productUnary budgetRoute
  have regseqUnary : UnaryHistory regseqSeal :=
    unary_cont_closed budgetUnary classifierUnary regseqRoute
  have sourceAtRadius :
      hsame radiusLedger radiusLedger ∨ hsame radiusLedger budgetRead ∨
        hsame radiusLedger regseqSeal ∨ hsame radiusLedger product :=
    Or.inl (hsame_refl radiusLedger)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row radiusLedger ∨ hsame row budgetRead ∨
              hsame row regseqSeal ∨ hsame row product)
          (fun row : BHist =>
            hsame row radiusLedger ∨ hsame row budgetRead ∨
              hsame row regseqSeal ∨ hsame row product)
          (fun row : BHist =>
            PkgSig bundle regseqSeal pkg ∧
              (hsame row radiusLedger ∨ hsame row budgetRead ∨
                hsame row regseqSeal ∨ hsame row product))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro radiusLedger sourceAtRadius
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
        cases source with
        | inl rowRadius =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowRadius)
        | inr tail =>
            cases tail with
            | inl rowBudget =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowBudget))
            | inr tail =>
                cases tail with
                | inl rowRegseq =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowRegseq)))
                | inr rowProduct =>
                    exact Or.inr
                      (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowProduct)))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact And.intro regseqPkg source
  }
  exact
    ⟨cert, radiusAUnary, radiusBUnary, radiusLedgerUnary, productUnary, budgetUnary,
      regseqUnary, radiusRoute, budgetRoute, regseqRoute, namePkg, regseqPkg⟩

end BEDC.Derived.CauchyProductUp
