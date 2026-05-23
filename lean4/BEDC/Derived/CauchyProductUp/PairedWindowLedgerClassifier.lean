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

theorem CauchyProductPacket_paired_window_ledger_classifier [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes sealRead ->
        PkgSig bundle sealRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row classifier ∨ hsame row ledger)
              (fun row : BHist => hsame row classifier ∨ hsame row ledger)
              (fun row : BHist =>
                PkgSig bundle sealRead pkg ∧ (hsame row classifier ∨ hsame row ledger))
              hsame ∧
            UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
              UnaryHistory classifier ∧ UnaryHistory sealRead ∧ Cont windowA windowB transport ∧
                Cont observationA observationB product ∧ Cont product ledger classifier ∧
                  Cont classifier routes sealRead ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet classifierSeal sealReadPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed classifierUnary routesUnary classifierSeal
  have sourceAtClassifier :
      hsame classifier classifier ∨ hsame classifier ledger :=
    Or.inl (hsame_refl classifier)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifier ∨ hsame row ledger)
          (fun row : BHist => hsame row classifier ∨ hsame row ledger)
          (fun row : BHist =>
            PkgSig bundle sealRead pkg ∧ (hsame row classifier ∨ hsame row ledger))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifier sourceAtClassifier
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
        intro row _row' sameRows source
        cases source with
        | inl sameClassifier =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameClassifier)
        | inr sameLedger =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameLedger)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨sealReadPkg, source⟩
  }
  exact
    ⟨cert, windowAUnary, windowBUnary, productUnary, classifierUnary, sealReadUnary,
      windowTransport, productRoute, classifierRoute, classifierSeal, namePkg, sealReadPkg⟩

end BEDC.Derived.CauchyProductUp
