import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetaCICParallelDiamondFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive MetaCICParallelDiamondFrontierUp : Type where
  | mk :
      (premise peak join residual checker fragment bounded obstruction transport replay
        provenance localName : BHist) →
      MetaCICParallelDiamondFrontierUp

def MetacicParallelDiamondFrontierCarrier [AskSetup] [PackageSetup]
    (premise peak join residual checker fragment bounded obstruction transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory premise ∧ UnaryHistory peak ∧ UnaryHistory join ∧
    UnaryHistory residual ∧ UnaryHistory checker ∧ UnaryHistory fragment ∧
      UnaryHistory bounded ∧ UnaryHistory obstruction ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          PkgSig bundle provenance pkg

theorem MetacicParallelDiamondFrontierObligations [AskSetup] [PackageSetup]
    {premise peak join residual checker fragment bounded obstruction transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicParallelDiamondFrontierCarrier premise peak join residual checker fragment
        bounded obstruction transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            (hsame row premise ∨ hsame row peak ∨ hsame row join ∨
              hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row premise ∨ hsame row peak ∨ hsame row join ∨
              hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          hsame ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨premiseUnary, peakUnary, joinUnary, residualUnary, checkerUnary,
    fragmentUnary, boundedUnary, obstructionUnary, transportUnary, replayUnary,
    provenanceUnary, localNameUnary, provenancePkg⟩ := carrier
  have sourceWitness :
      (fun row : BHist =>
        (hsame row premise ∨ hsame row peak ∨ hsame row join ∨
          hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
            hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
              hsame row replay ∨ hsame row provenance ∨ hsame row localName) ∧
          UnaryHistory row) premise := by
    exact ⟨Or.inl (hsame_refl premise), premiseUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row premise ∨ hsame row peak ∨ hsame row join ∨
              hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row premise ∨ hsame row peak ∨ hsame row join ∨
              hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro premise sourceWitness
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }
  exact ⟨cert, provenancePkg⟩

end BEDC.Derived.MetaCICParallelDiamondFrontierUp
