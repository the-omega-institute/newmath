import BEDC.Derived.LargeModelCorpusSupplyUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LargeModelCorpusSupplyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LargeModelCorpusSupplyProvenanceBoundary [AskSetup] [PackageSetup]
    {R F W I A H K P N sourceRead weightRead inferenceRead auditRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory F →
        UnaryHistory W →
          UnaryHistory I →
            UnaryHistory A →
              Cont R F sourceRead →
                Cont sourceRead W weightRead →
                  Cont weightRead I inferenceRead →
                    Cont inferenceRead A auditRead →
                      Cont auditRead K namedRead →
                        PkgSig bundle P pkg →
                          UnaryHistory sourceRead ∧
                            UnaryHistory weightRead ∧
                              UnaryHistory inferenceRead ∧
                                UnaryHistory auditRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro rUnary fUnary wUnary iUnary aUnary sourceRoute weightRoute inferenceRoute
    auditRoute _namedRoute provenancePkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed rUnary fUnary sourceRoute
  have weightUnary : UnaryHistory weightRead :=
    unary_cont_closed sourceUnary wUnary weightRoute
  have inferenceUnary : UnaryHistory inferenceRead :=
    unary_cont_closed weightUnary iUnary inferenceRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed inferenceUnary aUnary auditRoute
  exact ⟨sourceUnary, weightUnary, inferenceUnary, auditUnary, provenancePkg⟩

end BEDC.Derived.LargeModelCorpusSupplyUp
