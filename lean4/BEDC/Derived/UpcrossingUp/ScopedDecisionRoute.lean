import BEDC.Derived.UpcrossingUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UpcrossingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpcrossingScopedDecisionRoute [AskSetup] [PackageSetup]
    {source martingale window threshold route provenance localCert routeRead decisionRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UpcrossingCarrier source martingale window threshold route provenance localCert bundle pkg →
      Cont martingale window routeRead →
        Cont routeRead threshold decisionRead →
          PkgSig bundle decisionRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row decisionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row martingale ∨ hsame row window ∨ hsame row threshold ∨
                    hsame row decisionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont martingale window routeRead ∧
                    Cont routeRead threshold decisionRead ∧ PkgSig bundle decisionRead pkg)
                hsame ∧
              UnaryHistory routeRead ∧ UnaryHistory decisionRead ∧
                Cont martingale window routeRead ∧ Cont routeRead threshold decisionRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle decisionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier martingaleWindow routeThreshold decisionPkg
  obtain ⟨_sourceUnary, martingaleUnary, windowUnary, thresholdUnary, _routeUnary,
    _provenanceUnary, _localCertUnary, provenancePkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed martingaleUnary windowUnary martingaleWindow
  have decisionReadUnary : UnaryHistory decisionRead :=
    unary_cont_closed routeReadUnary thresholdUnary routeThreshold
  have sourceDecision :
      (fun row : BHist => hsame row decisionRead ∧ UnaryHistory row) decisionRead := by
    exact ⟨hsame_refl decisionRead, decisionReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row decisionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row martingale ∨ hsame row window ∨ hsame row threshold ∨
              hsame row decisionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont martingale window routeRead ∧
              Cont routeRead threshold decisionRead ∧ PkgSig bundle decisionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro decisionRead sourceDecision
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, martingaleWindow, routeThreshold, decisionPkg⟩
  }
  exact
    ⟨cert, routeReadUnary, decisionReadUnary, martingaleWindow, routeThreshold,
      provenancePkg, decisionPkg⟩

end BEDC.Derived.UpcrossingUp
