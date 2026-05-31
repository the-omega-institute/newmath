import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_pvariation_window_bound [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name variationWindow
      variationSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg ->
      Cont windows tolerance variationWindow ->
        Cont variationWindow readback variationSeal ->
          PkgSig bundle variationSeal pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row variationSeal ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont filter windows tolerance ∧ Cont windows tolerance variationWindow ∧
                  Cont variationWindow readback variationSeal)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle variationSeal pkg ∧
                  hsame row variationSeal)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet windowsToleranceVariation variationReadbackSeal variationPkg
  obtain ⟨_filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have variationWindowUnary : UnaryHistory variationWindow :=
    unary_cont_closed windowsUnary toleranceUnary windowsToleranceVariation
  have variationSealUnary : UnaryHistory variationSeal :=
    unary_cont_closed variationWindowUnary readbackUnary variationReadbackSeal
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro variationSeal
          ⟨hsame_refl variationSeal, variationSealUnary⟩
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
      intro _row _source
      exact ⟨filterWindows, windowsToleranceVariation, variationReadbackSeal⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, variationPkg, source.left⟩
  }

end BEDC.Derived.CauchyfiltercompletionUp
