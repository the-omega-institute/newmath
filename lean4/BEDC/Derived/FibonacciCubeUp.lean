import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FibonacciCubeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FibonacciCubeCarrier [AskSetup] [PackageSetup]
    (length path word support deps cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory path ∧ Cont length path word ∧
    Cont word BHist.Empty deps ∧ Cont deps BHist.Empty cert ∧ PkgSig bundle cert pkg

theorem FibonacciCubeCarrier_habitation [AskSetup] [PackageSetup]
    {length path word deps cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory length ->
      UnaryHistory path ->
        Cont length path word ->
          Cont word BHist.Empty deps ->
            Cont deps BHist.Empty cert ->
              PkgSig bundle cert pkg ->
                FibonacciCubeCarrier length path word BHist.Empty deps cert bundle pkg ∧
                  UnaryHistory word ∧ UnaryHistory deps ∧ UnaryHistory cert := by
  intro lengthUnary pathUnary lengthPathWord wordEmptyDeps depsEmptyCert certPkg
  have wordUnary : UnaryHistory word :=
    unary_cont_closed lengthUnary pathUnary lengthPathWord
  have emptyUnary : UnaryHistory BHist.Empty :=
    unary_empty
  have depsUnary : UnaryHistory deps :=
    unary_cont_closed wordUnary emptyUnary wordEmptyDeps
  have certUnary : UnaryHistory cert :=
    unary_cont_closed depsUnary emptyUnary depsEmptyCert
  exact
    ⟨⟨lengthUnary, pathUnary, lengthPathWord, wordEmptyDeps, depsEmptyCert, certPkg⟩,
      wordUnary, depsUnary, certUnary⟩

end BEDC.Derived.FibonacciCubeUp
