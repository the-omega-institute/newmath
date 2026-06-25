import BEDC.Derived.RiemannStieltjesUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RiemannStieltjesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannStieltjesDarbouxMeshRefinement [AskSetup] [PackageSetup]
    {partition mesh refinement integrator regulated value refinedValue _provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory partition ->
      UnaryHistory mesh ->
        UnaryHistory refinement ->
          UnaryHistory integrator ->
            UnaryHistory regulated ->
              Cont partition mesh refinement ->
                Cont refinement integrator value ->
                  Cont value regulated refinedValue ->
                    PkgSig bundle refinedValue pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row refinedValue ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row partition ∨ hsame row mesh ∨
                              hsame row refinement ∨ hsame row integrator ∨
                                hsame row regulated ∨ hsame row value ∨
                                  hsame row refinedValue)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont partition mesh refinement ∧
                              Cont refinement integrator value ∧
                                Cont value regulated refinedValue ∧
                                  PkgSig bundle refinedValue pkg)
                          hsame ∧
                        UnaryHistory value ∧ UnaryHistory refinedValue := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro _partitionUnary _meshUnary refinementUnary integratorUnary regulatedUnary
    partitionMeshRefinement refinementIntegratorValue valueRegulatedRefined refinedPkg
  have valueUnary : UnaryHistory value :=
    unary_cont_closed refinementUnary integratorUnary refinementIntegratorValue
  have refinedValueUnary : UnaryHistory refinedValue :=
    unary_cont_closed valueUnary regulatedUnary valueRegulatedRefined
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinedValue ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row partition ∨ hsame row mesh ∨ hsame row refinement ∨
              hsame row integrator ∨ hsame row regulated ∨ hsame row value ∨
                hsame row refinedValue)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont partition mesh refinement ∧
              Cont refinement integrator value ∧ Cont value regulated refinedValue ∧
                PkgSig bundle refinedValue pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refinedValue ⟨hsame_refl refinedValue, refinedValueUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, partitionMeshRefinement, refinementIntegratorValue,
          valueRegulatedRefined, refinedPkg⟩
  }
  exact ⟨cert, valueUnary, refinedValueUnary⟩

end BEDC.Derived.RiemannStieltjesUp
