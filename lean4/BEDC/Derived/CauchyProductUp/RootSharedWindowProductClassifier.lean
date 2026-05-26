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

theorem CauchyProductPacket_root_shared_window_product_classifier_certificate
    [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
              hsame row classifier)
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
              hsame row classifier)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧
              (hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
                hsame row classifier))
          hsame ∧
        UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
          UnaryHistory classifier ∧ Cont windowA windowB transport ∧
            Cont observationA observationB product ∧ Cont product ledger classifier := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have sourceAtWindowA :
      hsame windowA windowA ∨ hsame windowA windowB ∨ hsame windowA product ∨
        hsame windowA classifier :=
    Or.inl (hsame_refl windowA)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
              hsame row classifier)
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
              hsame row classifier)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧
              (hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
                hsame row classifier))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro windowA sourceAtWindowA
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
        | inl rowWindowA =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowWindowA)
        | inr tail =>
            cases tail with
            | inl rowWindowB =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowWindowB))
            | inr tail =>
                cases tail with
                | inl rowProduct =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowProduct)))
                | inr rowClassifier =>
                    exact Or.inr
                      (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowClassifier)))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact And.intro namePkg source
  }
  exact
    ⟨cert, windowAUnary, windowBUnary, productUnary, classifierUnary, windowTransport,
      productRoute, classifierRoute⟩

end BEDC.Derived.CauchyProductUp
