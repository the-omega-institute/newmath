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

theorem CauchyProductPacket_multiplication_public_consumer_boundary [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        PkgSig bundle realSeal pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                  hsame row ledger)
              (fun row : BHist =>
                hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                  hsame row ledger)
              (fun row : BHist =>
                PkgSig bundle realSeal pkg ∧
                  (hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                    hsame row ledger))
              hsame ∧
            UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory realSeal ∧
              Cont observationA observationB product ∧ Cont product ledger classifier ∧
                Cont classifier routes realSeal ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet classifierRoutesRealSeal realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRealSeal
  have sourceAtRealSeal :
      hsame realSeal product ∨ hsame realSeal classifier ∨ hsame realSeal realSeal ∨
        hsame realSeal ledger :=
    Or.inr (Or.inr (Or.inl (hsame_refl realSeal)))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
              hsame row ledger)
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
              hsame row ledger)
          (fun row : BHist =>
            PkgSig bundle realSeal pkg ∧
              (hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                hsame row ledger))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceAtRealSeal
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
            | inr tail =>
                cases tail with
                | inl rowRealSeal =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowRealSeal)))
                | inr rowLedger =>
                    exact Or.inr
                      (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowLedger)))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact And.intro realSealPkg source
  }
  exact
    ⟨cert, productUnary, classifierUnary, realSealUnary, productRoute, classifierRoute,
      classifierRoutesRealSeal, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
