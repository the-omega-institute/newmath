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

theorem CauchyProductPacket_root_window_seal_stability [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name regseqSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes regseqSeal ->
        Cont regseqSeal ledger realSeal ->
          PkgSig bundle realSeal pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row product ∨ hsame row classifier ∨ hsame row realSeal)
                (fun row : BHist =>
                  hsame row product ∨ hsame row classifier ∨ hsame row realSeal)
                (fun row : BHist =>
                  PkgSig bundle realSeal pkg ∧
                    (hsame row product ∨ hsame row classifier ∨ hsame row realSeal))
                hsame ∧
              UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
                UnaryHistory classifier ∧ UnaryHistory regseqSeal ∧ UnaryHistory realSeal ∧
                  Cont windowA windowB transport ∧ Cont observationA observationB product ∧
                    Cont product ledger classifier ∧ Cont classifier routes regseqSeal ∧
                      Cont regseqSeal ledger realSeal ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet classifierRoutesSeal regseqSealRealSeal realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesSeal
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqSealUnary ledgerUnary regseqSealRealSeal
  have sourceAtProduct :
      hsame product product ∨ hsame product classifier ∨ hsame product realSeal :=
    Or.inl (hsame_refl product)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row realSeal)
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row realSeal)
          (fun row : BHist =>
            PkgSig bundle realSeal pkg ∧
              (hsame row product ∨ hsame row classifier ∨ hsame row realSeal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro product sourceAtProduct
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
        | inl rowProduct =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowProduct)
        | inr tail =>
          cases tail with
          | inl rowClassifier =>
              exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowClassifier))
          | inr rowRealSeal =>
              exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowRealSeal))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      cases source with
      | inl rowProduct =>
          exact ⟨realSealPkg, Or.inl rowProduct⟩
      | inr tail =>
          cases tail with
          | inl rowClassifier =>
              exact ⟨realSealPkg, Or.inr (Or.inl rowClassifier)⟩
          | inr rowRealSeal =>
              exact ⟨realSealPkg, Or.inr (Or.inr rowRealSeal)⟩
  }
  exact
    ⟨cert, windowAUnary, windowBUnary, productUnary, classifierUnary, regseqSealUnary,
      realSealUnary, windowTransport, productRoute, classifierRoute, classifierRoutesSeal,
      regseqSealRealSeal, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
