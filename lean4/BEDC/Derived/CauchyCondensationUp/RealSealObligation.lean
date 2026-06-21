import BEDC.Derived.CauchyCondensationUp.RegSeqRatReadbackObligation

namespace BEDC.Derived.CauchyCondensationUp.RealSealObligation

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCondensationCarrier_real_seal_nonescape_obligation [AskSetup]
    [PackageSetup]
    {source windows blocks sums tails readback sealRow transportRow replayRow provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCondensationCarrier source windows blocks sums tails readback sealRow transportRow
        replayRow provenance localName bundle pkg ->
      Cont tails readback sealRow ->
        PkgSig bundle sealRow pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
              (fun row : BHist => hsame row tails ∨ hsame row readback ∨ hsame row sealRow)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont tails readback sealRow ∧ PkgSig bundle sealRow pkg)
              hsame ∧ UnaryHistory sealRow := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier tailsReadbackSeal sealPkg
  obtain ⟨_sourceUnary, _windowsUnary, _blocksUnary, _sumsUnary, tailsUnary, readbackUnary,
    sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkg, _localNamePkg⟩ := carrier
  have sourceSeal :
      (fun row : BHist => hsame row sealRow ∧ UnaryHistory row) sealRow := by
    exact ⟨hsame_refl sealRow, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tails ∨ hsame row readback ∨ hsame row sealRow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tails readback sealRow ∧ PkgSig bundle sealRow pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceSeal
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, tailsReadbackSeal, sealPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.CauchyCondensationUp.RealSealObligation
