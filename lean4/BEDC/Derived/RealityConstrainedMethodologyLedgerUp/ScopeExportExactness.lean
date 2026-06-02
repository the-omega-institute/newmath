import BEDC.Derived.RealityConstrainedMethodologyLedgerUp.KernelCarrier

namespace BEDC.Derived.RealityConstrainedMethodologyLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealityConstrainedMethodologyLedgerScopeExportExactness [AskSetup] [PackageSetup]
    {X A O T I S D U F H C Q N scopeRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedMethodologyLedgerCarrier X A O T I S D U F H C Q N bundle pkg →
      Cont S D scopeRead →
        Cont scopeRead U exportRead →
          PkgSig bundle exportRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row D ∨ hsame row U ∨ hsame row scopeRead ∨
                    hsame row exportRead)
                (fun row : BHist =>
                  hsame row exportRead ∧ PkgSig bundle exportRead pkg ∧
                    Cont scopeRead U exportRead)
                hsame ∧
              UnaryHistory scopeRead ∧ UnaryHistory exportRead ∧ PkgSig bundle Q pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier scopeCont exportCont exportPkg
  obtain ⟨_xUnary, _aUnary, _oUnary, _tUnary, _iUnary, scopeUnary, refusalUnary,
    upgradeUnary, _failureUnary, _scopeAppendSame, _scopeRefusalUpgrade,
    _upgradeFailureConsumer, _consumerProvenanceName, qPkg⟩ := carrier
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed scopeUnary refusalUnary scopeCont
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed scopeReadUnary upgradeUnary exportCont
  have sourceExport :
      (fun row : BHist => hsame row exportRead ∧ UnaryHistory row) exportRead := by
    exact ⟨hsame_refl exportRead, exportReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row D ∨ hsame row U ∨ hsame row scopeRead ∨
              hsame row exportRead)
          (fun row : BHist =>
            hsame row exportRead ∧ PkgSig bundle exportRead pkg ∧
              Cont scopeRead U exportRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead sourceExport
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
      exact ⟨source.left, exportPkg, exportCont⟩
  }
  exact ⟨cert, scopeReadUnary, exportReadUnary, qPkg⟩

end BEDC.Derived.RealityConstrainedMethodologyLedgerUp
