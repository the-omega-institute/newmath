import BEDC.Derived.ScientificObjectUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ScientificObjectUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive ScientificObjectObligationRoute
    (R K I L B G A T O D H C P N : BHist) : BHist → Prop where
  | recordClassifier :
      Cont R K H → ScientificObjectObligationRoute R K I L B G A T O D H C P N H
  | gapReport :
      Cont L B G → ScientificObjectObligationRoute R K I L B G A T O D H C P N G
  | truthDomain :
      Cont T D N → ScientificObjectObligationRoute R K I L B G A T O D H C P N N

theorem ScientificObjectObligationClosurePackage [AskSetup] [PackageSetup]
    {R K I L B G A T O D H C P N row : BHist} :
    UnaryHistory R →
      UnaryHistory K →
        UnaryHistory L →
          UnaryHistory B →
            UnaryHistory T →
              UnaryHistory D →
                ScientificObjectObligationRoute R K I L B G A T O D H C P N row →
                  UnaryHistory row ∧ (hsame row H ∨ hsame row G ∨ hsame row N) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro rUnary kUnary lUnary bUnary tUnary dUnary route
  cases route with
  | recordClassifier recordRoute =>
      exact ⟨unary_cont_closed rUnary kUnary recordRoute, Or.inl (hsame_refl H)⟩
  | gapReport gapRoute =>
      exact ⟨unary_cont_closed lUnary bUnary gapRoute, Or.inr (Or.inl (hsame_refl G))⟩
  | truthDomain truthRoute =>
      exact ⟨unary_cont_closed tUnary dUnary truthRoute, Or.inr (Or.inr (hsame_refl N))⟩

end BEDC.Derived.ScientificObjectUp
