import BEDC.Derived.DenseUniformEmbeddingUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DenseUniformEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DenseUniformEmbeddingCarrier [AskSetup] [PackageSetup]
    (source target imageWitness modulus handoff extension compatibility transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory imageWitness ∧
    UnaryHistory modulus ∧ UnaryHistory handoff ∧ UnaryHistory extension ∧
      UnaryHistory compatibility ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont source imageWitness modulus ∧ Cont modulus handoff extension ∧
            Cont compatibility transport replay ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem DenseUniformEmbeddingCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {source target imageWitness modulus handoff extension compatibility transport replay provenance
      localName sink : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DenseUniformEmbeddingCarrier source target imageWitness modulus handoff extension compatibility
      transport replay provenance localName bundle pkg ->
      Cont source target sink ->
        PkgSig bundle sink pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row sink ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row source ∨ hsame row target ∨ hsame row imageWitness ∨
                hsame row modulus ∨ hsame row handoff ∨ hsame row extension ∨
                  hsame row compatibility ∨ hsame row sink)
            (fun row : BHist => hsame row sink ∧ PkgSig bundle sink pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory SemanticNameCert
  intro carrier sourceTarget sinkPkg
  exact {
    core := {
      carrier_inhabited := by
        have sourceUnary : UnaryHistory source := carrier.left
        have targetUnary : UnaryHistory target := carrier.right.left
        have sinkUnary : UnaryHistory sink :=
          unary_cont_closed sourceUnary targetUnary sourceTarget
        exact Exists.intro sink ⟨hsame_refl sink, sinkUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, sinkPkg⟩
  }

end BEDC.Derived.DenseUniformEmbeddingUp
