import BEDC.Derived.PredictiveDescentUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PredictiveDescentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PredictiveDescentStabilityScope [AskSetup] [PackageSetup]
    {F O K A S X H C P N opRead scopeRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    Cont O A opRead ->
      Cont A K scopeRead ->
        PkgSig bundle P pkg ->
          UnaryHistory O ->
            UnaryHistory A ->
              UnaryHistory K ->
                UnaryHistory opRead ∧
                  UnaryHistory scopeRead ∧
                    Cont O A opRead ∧ Cont A K scopeRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro opCont scopeCont provenancePkg observedUnary operationUnary continuationUnary
  have opReadUnary : UnaryHistory opRead :=
    unary_cont_closed observedUnary operationUnary opCont
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed operationUnary continuationUnary scopeCont
  exact ⟨opReadUnary, scopeReadUnary, opCont, scopeCont, provenancePkg⟩

end BEDC.Derived.PredictiveDescentUp
