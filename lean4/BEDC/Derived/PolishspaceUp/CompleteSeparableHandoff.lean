import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompleteSeparableHandoff [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance localName
      completionRead separableRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg →
      Cont metric complete completionRead →
        Cont metric separable separableRead →
          Cont completionRead separableRead handoffRead →
            PkgSig bundle handoffRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                      hsame row stream ∨ hsame row readback ∨ hsame row handoffRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle handoffRead pkg)
                  hsame ∧
                UnaryHistory completionRead ∧ UnaryHistory separableRead ∧
                  UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier metricCompleteRead metricSeparableRead completeSeparableHandoff handoffPkg
  obtain ⟨metricUnary, completeUnary, separableUnary, _streamUnary, _readbackUnary,
    _ledgerUnary, _alignmentUnary, _transportUnary, _metricCompleteAlignment,
    _alignmentStreamReadback, _ledgerTransportRoute, provenancePkg⟩ := carrier
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricCompleteRead
  have separableReadUnary : UnaryHistory separableRead :=
    unary_cont_closed metricUnary separableUnary metricSeparableRead
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed completionReadUnary separableReadUnary completeSeparableHandoff
  have sourceHandoff :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoff
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, handoffPkg⟩
  }
  exact ⟨cert, completionReadUnary, separableReadUnary, handoffReadUnary⟩

end BEDC.Derived.PolishspaceUp
