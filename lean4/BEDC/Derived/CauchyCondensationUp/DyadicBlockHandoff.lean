import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCondensationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCondensationCarrier [AskSetup] [PackageSetup]
    (source windows blocks sums tails _readback sealRow transportRow replayRow provenance localName :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory source ∧ UnaryHistory windows ∧ UnaryHistory blocks ∧
    UnaryHistory sums ∧ UnaryHistory tails ∧ UnaryHistory sealRow ∧
      UnaryHistory transportRow ∧ UnaryHistory replayRow ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem CauchyCondensationCarrier_dyadic_block_handoff [AskSetup] [PackageSetup]
    {source windows blocks sums tails readback sealRow transportRow replayRow provenance localName
      blockRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCondensationCarrier source windows blocks sums tails readback sealRow transportRow replayRow
        provenance localName bundle pkg ->
      Cont windows blocks blockRead ->
        Cont blockRead sums tailRead ->
          Cont tailRead tails readback ->
            PkgSig bundle readback pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row blockRead ∨ hsame row tailRead ∨ hsame row readback) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row windows ∨ hsame row blocks ∨
                      hsame row sums ∨ hsame row tails ∨ hsame row blockRead ∨
                        hsame row tailRead ∨ hsame row readback)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont windows blocks blockRead ∧
                      Cont blockRead sums tailRead ∧ Cont tailRead tails readback ∧
                        PkgSig bundle readback pkg)
                  hsame ∧ UnaryHistory blockRead ∧ UnaryHistory tailRead ∧
                UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier windowsBlocks blockSums tailTails readbackPkg
  obtain ⟨_sourceUnary, windowsUnary, blocksUnary, sumsUnary, tailsUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _provenancePkg,
    _localNamePkg⟩ := carrier
  have blockReadUnary : UnaryHistory blockRead :=
    unary_cont_closed windowsUnary blocksUnary windowsBlocks
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed blockReadUnary sumsUnary blockSums
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed tailReadUnary tailsUnary tailTails
  have sourceReadback :
      (fun row : BHist =>
        (hsame row blockRead ∨ hsame row tailRead ∨ hsame row readback) ∧
          UnaryHistory row)
        readback := by
    exact ⟨Or.inr (Or.inr (hsame_refl readback)), readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row blockRead ∨ hsame row tailRead ∨ hsame row readback) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row windows ∨ hsame row blocks ∨ hsame row sums ∨
              hsame row tails ∨ hsame row blockRead ∨ hsame row tailRead ∨
                hsame row readback)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont windows blocks blockRead ∧ Cont blockRead sums tailRead ∧
              Cont tailRead tails readback ∧ PkgSig bundle readback pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro readback sourceReadback
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
              (fun blockRow =>
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl blockRow))))))
              (fun rest => Or.elim rest
                (fun tailRow =>
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl tailRow)))))))
                (fun readbackRow =>
                  Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inr readbackRow))))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, windowsBlocks, blockSums, tailTails, readbackPkg⟩
    }
  exact ⟨cert, blockReadUnary, tailReadUnary, readbackUnary⟩

theorem CauchyCondensationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source windows blocks sums tails readback sealRow transportRow replayRow provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCondensationCarrier source windows blocks sums tails readback sealRow transportRow replayRow
        provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row windows ∨ hsame row blocks ∨ hsame row sums ∨
              hsame row tails ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row provenance ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame ∧ UnaryHistory source ∧ UnaryHistory windows ∧ UnaryHistory blocks ∧
        UnaryHistory sums ∧ UnaryHistory tails ∧ UnaryHistory sealRow ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory SemanticNameCert hsame
  intro carrier
  obtain ⟨sourceUnary, windowsUnary, blocksUnary, sumsUnary, tailsUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, localNameUnary, provenancePkg,
    localNamePkg⟩ := carrier
  have localSource :
      (fun row : BHist => hsame row localName ∧ UnaryHistory row) localName := by
    exact ⟨hsame_refl localName, localNameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row windows ∨ hsame row blocks ∨ hsame row sums ∨
              hsame row tails ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row provenance ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localName localSource
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
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr sourceRow.left)))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, sourceUnary, windowsUnary, blocksUnary, sumsUnary, tailsUnary, sealUnary,
    provenancePkg, localNamePkg⟩

end BEDC.Derived.CauchyCondensationUp
