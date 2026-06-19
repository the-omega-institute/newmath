import BEDC.Derived.CauchyCondensationUp.DyadicBlockHandoff

namespace BEDC.Derived.CauchyCondensationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCondensationCarrier_dyadic_block_tail_transport [AskSetup] [PackageSetup]
    {source windows blocks sums tails readback sealRow transportRow replayRow provenance localName
      blockRead tailRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCondensationCarrier source windows blocks sums tails readback sealRow transportRow replayRow
        provenance localName bundle pkg ->
      Cont windows blocks blockRead ->
        Cont blockRead sums tailRead ->
          Cont tailRead tails readbackRead ->
            Cont readbackRead sealRow sealRead ->
              PkgSig bundle sealRead pkg ->
                hsame readbackRead readback ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row readbackRead ∨ hsame row sealRead) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row windows ∨ hsame row blocks ∨ hsame row sums ∨
                          hsame row tails ∨ hsame row readbackRead ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont tailRead tails readbackRead ∧
                          Cont readbackRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
                      hsame ∧ UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier windowsBlocks blockSums tailTails readbackSeal sealPkg sameReadback
  obtain ⟨_sourceUnary, windowsUnary, blocksUnary, sumsUnary, tailsUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, provenancePkg,
    _localNamePkg⟩ := carrier
  have blockReadUnary : UnaryHistory blockRead :=
    unary_cont_closed windowsUnary blocksUnary windowsBlocks
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed blockReadUnary sumsUnary blockSums
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed tailReadUnary tailsUnary tailTails
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary sealUnary readbackSeal
  have readbackSource :
      (fun row : BHist => (hsame row readbackRead ∨ hsame row sealRead) ∧ UnaryHistory row)
        readbackRead := by
    exact ⟨Or.inl (hsame_refl readbackRead), readbackReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row readbackRead ∨ hsame row sealRead) ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row windows ∨ hsame row blocks ∨ hsame row sums ∨ hsame row tails ∨
              hsame row readbackRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tailRead tails readbackRead ∧
              Cont readbackRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro readbackRead readbackSource
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
          cases sameRows
          exact sourceRow
      }
      pattern_sound := by
        intro row sourceRow
        cases sourceRow with
        | intro sourceRows _sourceUnary =>
            exact Or.elim sourceRows
              (fun readbackRow =>
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inl readbackRow)))))
              (fun sealRow =>
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sealRow)))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, tailTails, readbackSeal, sealPkg⟩
    }
  exact ⟨cert, readbackReadUnary, sealReadUnary, provenancePkg⟩

end BEDC.Derived.CauchyCondensationUp
