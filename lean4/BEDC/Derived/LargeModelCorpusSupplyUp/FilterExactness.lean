import BEDC.Derived.LargeModelCorpusSupplyUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LargeModelCorpusSupplyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LargeModelCorpusSupplyFilterExactness [AskSetup] [PackageSetup]
    {R F W I A H K P N filterRead weightRead inferenceRead auditRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R → UnaryHistory F → UnaryHistory W → UnaryHistory I → UnaryHistory A →
      Cont R F filterRead → Cont filterRead W weightRead →
        Cont weightRead I inferenceRead → Cont inferenceRead A auditRead →
          Cont auditRead K namedRead → PkgSig bundle P pkg →
            UnaryHistory filterRead ∧ UnaryHistory weightRead ∧
              UnaryHistory inferenceRead ∧ UnaryHistory auditRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro unaryR unaryF unaryW unaryI unaryA filterRoute weightRoute inferenceRoute auditRoute
    _namedRoute pkgSig
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed unaryR unaryF filterRoute
  have weightUnary : UnaryHistory weightRead :=
    unary_cont_closed filterUnary unaryW weightRoute
  have inferenceUnary : UnaryHistory inferenceRead :=
    unary_cont_closed weightUnary unaryI inferenceRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed inferenceUnary unaryA auditRoute
  exact ⟨filterUnary, weightUnary, inferenceUnary, auditUnary, pkgSig⟩

end BEDC.Derived.LargeModelCorpusSupplyUp
