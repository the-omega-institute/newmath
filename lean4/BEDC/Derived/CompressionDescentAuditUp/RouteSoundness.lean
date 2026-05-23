import BEDC.Derived.CompressionDescentAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompressionDescentAuditUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompressionDescentAuditRouteSoundness [AskSetup] [PackageSetup]
    {T E O D L F H P N routeRead ledgerRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    Cont T D routeRead ->
      Cont D L ledgerRead ->
        PkgSig bundle P pkg ->
          UnaryHistory T ->
            UnaryHistory D ->
              UnaryHistory L ->
                UnaryHistory routeRead ∧
                  UnaryHistory ledgerRead ∧
                    Cont T D routeRead ∧ Cont D L ledgerRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro routeCont ledgerCont provenancePkg towerUnary descentUnary ledgerUnary
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed towerUnary descentUnary routeCont
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed descentUnary ledgerUnary ledgerCont
  exact ⟨routeReadUnary, ledgerReadUnary, routeCont, ledgerCont, provenancePkg⟩

end BEDC.Derived.CompressionDescentAuditUp.TasteGate
