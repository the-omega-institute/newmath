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

theorem PolishSpaceStreamReadbackStability [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      streamRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceRootUnblockSurface metric complete separable stream readback ledger transport
        replay provenance localName bundle pkg →
      hsame streamRead stream →
        Cont streamRead readback transportedRead →
          PkgSig bundle transportedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                    hsame row replay ∨ hsame row transportedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle transportedRead pkg)
                hsame ∧
              UnaryHistory streamRead ∧ UnaryHistory transportedRead ∧
                UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro surface streamReadStream streamReadbackTransported transportedReadPkg
  obtain ⟨_metricUnary, _completeUnary, _separableUnary, streamUnary, readbackUnary,
    ledgerUnary, transportUnary, _metricComplete, _metricSeparable, ledgerTransportReplay,
    provenancePkg, _localNamePkg⟩ := surface
  have streamReadUnary : UnaryHistory streamRead :=
    unary_transport streamUnary (hsame_symm streamReadStream)
  have transportedReadUnary : UnaryHistory transportedRead :=
    unary_cont_closed streamReadUnary readbackUnary streamReadbackTransported
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportReplay
  have sourceTransportedRead :
      (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
          transportedRead := by
    exact ⟨hsame_refl transportedRead, transportedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
              hsame row replay ∨ hsame row transportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle transportedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro transportedRead sourceTransportedRead
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
      exact ⟨source.right, provenancePkg, transportedReadPkg⟩
  }
  exact ⟨cert, streamReadUnary, transportedReadUnary, replayUnary⟩

end BEDC.Derived.PolishspaceUp
