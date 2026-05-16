import BEDC.Derived.FiniteNetMinimumFoldUp

namespace BEDC.Derived.FiniteNetMinimumFoldUp.HandoffGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteNetMinimumFoldPacket_uniformmodulus_compactmetric_handoff_gate
    [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow compactInput folded
      lowerExport handoff uniformOutput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont bundleRow radius compactInput →
        Cont compactInput accumulator folded →
          Cont folded lower lowerExport →
            Cont accumulator lower handoff →
              hsame uniformOutput handoff →
                PkgSig bundle lowerExport pkg →
                  PkgSig bundle handoff pkg →
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row uniformOutput ∧ UnaryHistory row ∧
                          PkgSig bundle handoff pkg)
                      (fun row : BHist => hsame row handoff ∧ Cont accumulator lower handoff)
                      (fun _row : BHist =>
                        Cont bundleRow radius compactInput ∧
                          Cont compactInput accumulator folded ∧
                            Cont folded lower lowerExport ∧
                              Cont transport nameRow provenance ∧
                                PkgSig bundle lowerExport pkg ∧ PkgSig bundle handoff pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet bundleRadiusCompact compactAccumulatorFolded foldedLowerExport
    accumulatorLowerHandoff outputSame lowerExportPkg handoffPkg
  obtain ⟨_bundleRowUnary, _radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, _accumulatorLowerTransport, transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _provenancePkg⟩ := packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed accumulatorUnary lowerUnary accumulatorLowerHandoff
  have uniformOutputUnary : UnaryHistory uniformOutput :=
    unary_transport_symm handoffUnary outputSame
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro uniformOutput
          ⟨hsame_refl uniformOutput, uniformOutputUnary, handoffPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right.left same, source.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨hsame_trans source.left outputSame, accumulatorLowerHandoff⟩
    ledger_sound := by
      intro _row _source
      exact
        ⟨bundleRadiusCompact, compactAccumulatorFolded, foldedLowerExport,
          transportNameProvenance, lowerExportPkg, handoffPkg⟩
  }

end BEDC.Derived.FiniteNetMinimumFoldUp.HandoffGate
