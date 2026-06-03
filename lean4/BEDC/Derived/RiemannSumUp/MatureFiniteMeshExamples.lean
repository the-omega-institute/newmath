import BEDC.Derived.RiemannSumUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RiemannSumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannSumCarrier_mature_finite_mesh_examples [AskSetup] [PackageSetup]
    {M T F W S H C P N exampleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSumCarrier M T F W S H C P N bundle pkg ->
      Cont M T F ->
        Cont F W S ->
          Cont S C exampleRead ->
            PkgSig bundle exampleRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row exampleRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row W ∨
                      hsame row S ∨ Cont M T F ∨ Cont F W S ∨ Cont S C exampleRead)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle exampleRead pkg ∧ hsame row exampleRead)
                  hsame ∧
                UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory F ∧ UnaryHistory W ∧
                  UnaryHistory S ∧ UnaryHistory exampleRead ∧ Cont M T F ∧ Cont F W S ∧
                    Cont S C exampleRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg ∧ PkgSig bundle exampleRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier meshTagValue valueWidthSum sumReplayExample examplePkg
  obtain ⟨meshUnary, tagUnary, valueUnary, widthUnary, _transportUnary, replayUnary,
    provenanceUnary, localNameUnary, _carrierMeshTagValue, _carrierValueWidthSum,
    _transportReplayProvenance, provenancePkg, localNamePkg⟩ := carrier
  have sumUnary : UnaryHistory S :=
    unary_cont_closed valueUnary widthUnary valueWidthSum
  have exampleUnary : UnaryHistory exampleRead :=
    unary_cont_closed sumUnary replayUnary sumReplayExample
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exampleRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row W ∨
              hsame row S ∨ Cont M T F ∨ Cont F W S ∨ Cont S C exampleRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
              PkgSig bundle exampleRead pkg ∧ hsame row exampleRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exampleRead ⟨hsame_refl exampleRead, exampleUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sumReplayExample))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, examplePkg, source.left⟩
  }
  exact
    ⟨cert, meshUnary, tagUnary, valueUnary, widthUnary, sumUnary, exampleUnary,
      meshTagValue, valueWidthSum, sumReplayExample, provenancePkg, localNamePkg,
      examplePkg⟩

end BEDC.Derived.RiemannSumUp
