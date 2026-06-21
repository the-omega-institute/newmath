import BEDC.Derived.CauchyCondensationUp.DyadicBlockHandoff

namespace BEDC.Derived.CauchyCondensationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCondensationCarrier_test_dyadic_block_equivalence [AskSetup] [PackageSetup]
    {source windows blocks sums tails readback sealRow transportRow replayRow provenance localName
      consumerRead blockRead tailRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCondensationCarrier source windows blocks sums tails readback sealRow transportRow
        replayRow provenance localName bundle pkg ->
      Cont windows blocks blockRead ->
        Cont blockRead sums tailRead ->
          Cont tailRead tails readbackRead ->
            Cont readbackRead sealRow sealRead ->
              Cont sealRead localName consumerRead ->
                PkgSig bundle consumerRead pkg ->
                  hsame readbackRead readback ->
                    SemanticNameCert
                        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row source ∨ hsame row windows ∨ hsame row blocks ∨
                            hsame row sums ∨ hsame row tails ∨ hsame row readbackRead ∨
                              hsame row sealRead ∨ hsame row consumerRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont windows blocks blockRead ∧
                            Cont blockRead sums tailRead ∧ Cont tailRead tails readbackRead ∧
                              Cont readbackRead sealRow sealRead ∧
                                Cont sealRead localName consumerRead ∧
                                  PkgSig bundle consumerRead pkg)
                        hsame ∧ UnaryHistory blockRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowsBlocks blockSums tailTails readbackSeal sealConsumer consumerPkg
    _readbackSame
  obtain ⟨_sourceUnary, windowsUnary, blocksUnary, sumsUnary, tailsUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _provenancePkg,
    _localNamePkg⟩ := carrier
  have blockReadUnary : UnaryHistory blockRead :=
    unary_cont_closed windowsUnary blocksUnary windowsBlocks
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed blockReadUnary sumsUnary blockSums
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed tailReadUnary tailsUnary tailTails
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary sealUnary readbackSeal
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealReadUnary localNameUnary sealConsumer
  have sourceAtConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row windows ∨ hsame row blocks ∨ hsame row sums ∨
              hsame row tails ∨ hsame row readbackRead ∨ hsame row sealRead ∨
                hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont windows blocks blockRead ∧ Cont blockRead sums tailRead ∧
              Cont tailRead tails readbackRead ∧ Cont readbackRead sealRow sealRead ∧
                Cont sealRead localName consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowsBlocks, blockSums, tailTails, readbackSeal, sealConsumer,
          consumerPkg⟩
  }
  exact
    ⟨cert, blockReadUnary, tailReadUnary, readbackReadUnary, sealReadUnary,
      consumerReadUnary⟩

end BEDC.Derived.CauchyCondensationUp
