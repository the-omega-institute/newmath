import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyModulusSharedWindowBudget [AskSetup] [PackageSetup]
    {S R D M W E budget witness endpoint : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory S -> UnaryHistory R -> UnaryHistory D -> UnaryHistory M ->
      UnaryHistory W -> UnaryHistory E -> Cont S R budget ->
        Cont budget D witness -> Cont M W E -> Cont witness E endpoint ->
          PkgSig bundle endpoint pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row M ∨
                    hsame row W ∨ hsame row E ∨ hsame row budget ∨
                      hsame row witness ∨ hsame row endpoint)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont S R budget ∧ Cont budget D witness ∧
                    Cont M W E ∧ Cont witness E endpoint ∧ PkgSig bundle endpoint pkg)
                hsame ∧ UnaryHistory budget ∧ UnaryHistory witness ∧
                  UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sUnary rUnary dUnary mUnary wUnary eUnary selectedReadback budgetWitness
    modulusSeal endpointRoute endpointPkg
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed sUnary rUnary selectedReadback
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed budgetUnary dUnary budgetWitness
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed witnessUnary eUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row M ∨
              hsame row W ∨ hsame row E ∨ hsame row budget ∨ hsame row witness ∨
                hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R budget ∧ Cont budget D witness ∧
              Cont M W E ∧ Cont witness E endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectedReadback, budgetWitness, modulusSeal, endpointRoute,
          endpointPkg⟩
  }
  exact ⟨cert, budgetUnary, witnessUnary, endpointUnary⟩

end BEDC.Derived.UniformCauchyModulusUp
