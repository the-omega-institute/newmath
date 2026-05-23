import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealityConstrainedTruthCertFailureRouting [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N failureName ledgerRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont F N failureName →
      Cont failureName L ledgerRead →
        Cont ledgerRead N exportRead →
          UnaryHistory F →
            UnaryHistory N →
              UnaryHistory L →
                PkgSig bundle exportRead pkg →
                  TasteGate.realityConstrainedTruthCertFields
                      (TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N) =
                    [S, Sigma, K, T, U, D, I, L, F, N] ∧
                    UnaryHistory failureName ∧ UnaryHistory ledgerRead ∧
                      UnaryHistory exportRead ∧ Cont F N failureName ∧
                        Cont failureName L ledgerRead ∧ Cont ledgerRead N exportRead ∧
                          PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro failureRoute ledgerRoute exportRoute unaryF unaryN unaryL exportPkg
  have failureUnary : UnaryHistory failureName :=
    unary_cont_closed unaryF unaryN failureRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed failureUnary unaryL ledgerRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed ledgerUnary unaryN exportRoute
  exact
    ⟨rfl, failureUnary, ledgerUnary, exportUnary, failureRoute, ledgerRoute, exportRoute,
      exportPkg⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
