import BEDC.Derived.MetaCICParallelDiamondFrontierUp

namespace BEDC.Derived.MetaCICParallelDiamondFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicParallelDiamondFrontierResidualJoinLocality [AskSetup] [PackageSetup]
    {premise peak join residual checker fragment bounded obstruction transport replay
      provenance localName localJoinRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicParallelDiamondFrontierCarrier premise peak join residual checker fragment
        bounded obstruction transport replay provenance localName bundle pkg →
      Cont join residual localJoinRead →
        Cont localJoinRead replay publicRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row premise ∨ hsame row peak ∨ hsame row join ∨
                      hsame row residual ∨ hsame row checker ∨ hsame row obstruction ∨
                        hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont join residual localJoinRead ∧
                      Cont localJoinRead replay publicRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory localJoinRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: MetacicParallelDiamondFrontierCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier joinResidual localJoinReplay provenancePkg publicPkg
  obtain ⟨_premiseUnary, _peakUnary, joinUnary, residualUnary, _checkerUnary,
    _fragmentUnary, _boundedUnary, _obstructionUnary, _transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _carrierProvenancePkg⟩ := carrier
  have localJoinUnary : UnaryHistory localJoinRead :=
    unary_cont_closed joinUnary residualUnary joinResidual
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed localJoinUnary replayUnary localJoinReplay
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row premise ∨ hsame row peak ∨ hsame row join ∨ hsame row residual ∨
              hsame row checker ∨ hsame row obstruction ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont join residual localJoinRead ∧
              Cont localJoinRead replay publicRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle publicRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        exact ⟨source.right, joinResidual, localJoinReplay, provenancePkg, publicPkg⟩
    }
  exact ⟨cert, localJoinUnary, publicUnary⟩

end BEDC.Derived.MetaCICParallelDiamondFrontierUp
