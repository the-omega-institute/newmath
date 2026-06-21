import BEDC.Derived.CauchyCondensationUp.DyadicTailObligation

namespace BEDC.Derived.CauchyCondensationUp.RegSeqRatReadbackObligation

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCondensationCarrier_regseqrat_readback_obligation [AskSetup] [PackageSetup]
    {source windows blocks sums tails readback sealRow transportRow replayRow provenance localName
      blockRead tailRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCondensationCarrier source windows blocks sums tails readback sealRow transportRow
        replayRow provenance localName bundle pkg →
      Cont windows blocks blockRead →
        Cont blockRead sums tailRead →
          Cont tailRead readback readbackRead →
            PkgSig bundle provenance pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row windows ∨ hsame row blocks ∨
                      hsame row sums ∨ hsame row tails ∨ hsame row readback ∨
                        hsame row readbackRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont windows blocks blockRead ∧
                      Cont blockRead sums tailRead ∧ Cont tailRead readback readbackRead ∧
                        PkgSig bundle provenance pkg)
                  hsame ∧ UnaryHistory blockRead ∧ UnaryHistory tailRead ∧
                UnaryHistory readbackRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier windowsBlocks blockSums tailReadback provenancePkg
  obtain ⟨_sourceUnary, windowsUnary, blocksUnary, sumsUnary, _tailsUnary, readbackUnary,
    _sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _carrierProvenancePkg, _localNamePkg⟩ := carrier
  have blockReadUnary : UnaryHistory blockRead :=
    unary_cont_closed windowsUnary blocksUnary windowsBlocks
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed blockReadUnary sumsUnary blockSums
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed tailReadUnary readbackUnary tailReadback
  have sourceReadback :
      (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row) readbackRead := by
    exact ⟨hsame_refl readbackRead, readbackReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row windows ∨ hsame row blocks ∨ hsame row sums ∨
              hsame row tails ∨ hsame row readback ∨ hsame row readbackRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont windows blocks blockRead ∧ Cont blockRead sums tailRead ∧
              Cont tailRead readback readbackRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readbackRead sourceReadback
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
        constructor
        · exact hsame_trans (hsame_symm sameRows) sourceRow.left
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, windowsBlocks, blockSums, tailReadback, provenancePkg⟩
  }
  exact ⟨cert, blockReadUnary, tailReadUnary, readbackReadUnary⟩

end BEDC.Derived.CauchyCondensationUp.RegSeqRatReadbackObligation
