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

theorem CauchyProductPacket_root_selector_ledger_exactness [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name selectorRow sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes selectorRow ->
        Cont selectorRow ledger sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row selectorRow ∨ hsame row ledger ∨ hsame row sealRead)
                (fun row : BHist =>
                  hsame row selectorRow ∨ hsame row ledger ∨ hsame row sealRead)
                (fun row : BHist =>
                  PkgSig bundle sealRead pkg ∧
                    (hsame row selectorRow ∨ hsame row ledger ∨ hsame row sealRead))
                hsame ∧
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory selectorRow ∧
                UnaryHistory sealRead ∧ Cont product ledger classifier ∧
                  Cont classifier routes selectorRow ∧ Cont selectorRow ledger sealRead ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet classifierSelector selectorLedgerSeal sealReadPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have selectorUnary : UnaryHistory selectorRow :=
    unary_cont_closed classifierUnary routesUnary classifierSelector
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed selectorUnary ledgerUnary selectorLedgerSeal
  have sourceAtSelector :
      hsame selectorRow selectorRow ∨ hsame selectorRow ledger ∨ hsame selectorRow sealRead :=
    Or.inl (hsame_refl selectorRow)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row selectorRow ∨ hsame row ledger ∨ hsame row sealRead)
          (fun row : BHist =>
            hsame row selectorRow ∨ hsame row ledger ∨ hsame row sealRead)
          (fun row : BHist =>
            PkgSig bundle sealRead pkg ∧
              (hsame row selectorRow ∨ hsame row ledger ∨ hsame row sealRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro selectorRow sourceAtSelector
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
        | inl sameSelector =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameSelector)
        | inr rest =>
            cases rest with
            | inl sameLedger =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameLedger))
            | inr sameSeal =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨sealReadPkg, source⟩
  }
  exact
    ⟨cert, productUnary, classifierUnary, selectorUnary, sealReadUnary, classifierRoute,
      classifierSelector, selectorLedgerSeal, namePkg, sealReadPkg⟩

end BEDC.Derived.CauchyProductUp
