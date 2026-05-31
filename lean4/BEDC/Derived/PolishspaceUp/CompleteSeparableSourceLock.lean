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

theorem PolishSpaceCompleteSeparableSourceLock [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      completionRead denseRead sourceLock : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceRootUnblockSurface metric complete separable stream readback ledger transport
        replay provenance localName bundle pkg →
      Cont metric complete completionRead →
        Cont metric separable denseRead →
          Cont replay readback sourceLock →
            SemanticNameCert
                (fun row : BHist => hsame row sourceLock ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                    hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                      hsame row sourceLock)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg)
                hsame ∧
              UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                UnaryHistory sourceLock := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface metricComplete metricSeparable replayReadbackLock
  obtain ⟨metricUnary, completeUnary, separableUnary, _streamUnary, readbackUnary,
    ledgerUnary, transportUnary, _metricCompleteRoot, _metricSeparableRoot,
    ledgerTransportReplay, provenancePkg, localNamePkg⟩ := surface
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricComplete
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary separableUnary metricSeparable
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportReplay
  have sourceLockUnary : UnaryHistory sourceLock :=
    unary_cont_closed replayUnary readbackUnary replayReadbackLock
  have sourceLocked :
      (fun row : BHist => hsame row sourceLock ∧ UnaryHistory row) sourceLock := by
    exact ⟨hsame_refl sourceLock, sourceLockUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceLock ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row sourceLock)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceLock sourceLocked
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, completionUnary, denseUnary, sourceLockUnary⟩

end BEDC.Derived.PolishspaceUp
