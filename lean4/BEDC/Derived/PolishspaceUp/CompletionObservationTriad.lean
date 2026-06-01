import BEDC.Derived.PolishspaceUp.RootUnblockSurface
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompletionObservationTriad [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      completionRead denseRead streamRead triadRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceRootUnblockSurface metric complete separable stream readback ledger transport
        replay provenance localName bundle pkg →
      Cont metric complete completionRead →
        Cont metric separable denseRead →
          Cont stream readback streamRead →
            Cont streamRead ledger triadRead →
              PkgSig bundle triadRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row triadRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                        hsame row completionRead ∨ hsame row denseRead ∨
                          hsame row triadRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle triadRead pkg)
                    hsame ∧
                  UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                    UnaryHistory streamRead ∧ UnaryHistory triadRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface metricComplete metricSeparable streamReadback streamReadLedger triadPkg
  obtain ⟨metricUnary, completeUnary, separableUnary, streamUnary, readbackUnary,
    ledgerUnary, _transportUnary, _metricCompleteRoot, _metricSeparableRoot,
    _ledgerTransportReplay, provenancePkg, _localNamePkg⟩ := surface
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricComplete
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary separableUnary metricSeparable
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed streamUnary readbackUnary streamReadback
  have triadUnary : UnaryHistory triadRead :=
    unary_cont_closed streamReadUnary ledgerUnary streamReadLedger
  have sourceTriad :
      (fun row : BHist => hsame row triadRead ∧ UnaryHistory row) triadRead := by
    exact ⟨hsame_refl triadRead, triadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row triadRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
              hsame row completionRead ∨ hsame row denseRead ∨ hsame row triadRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle triadRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro triadRead sourceTriad
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
      exact ⟨source.right, provenancePkg, triadPkg⟩
  }
  exact ⟨cert, completionUnary, denseUnary, streamReadUnary, triadUnary⟩

end BEDC.Derived.PolishspaceUp
