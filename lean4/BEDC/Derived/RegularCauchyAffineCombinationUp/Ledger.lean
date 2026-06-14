import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyAffineCombinationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAffineCombinationLedger [AskSetup] [PackageSetup]
    {leftScale rightScale sumRead E ledgerRead R readbackRead Z sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory leftScale →
      UnaryHistory rightScale →
        UnaryHistory E →
          UnaryHistory R →
            UnaryHistory Z →
              Cont leftScale rightScale sumRead →
                Cont sumRead E ledgerRead →
                  Cont ledgerRead R readbackRead →
                    Cont readbackRead Z sealRead →
                      PkgSig bundle sealRead pkg →
                        UnaryHistory sumRead ∧ UnaryHistory ledgerRead ∧
                          UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                            Cont leftScale rightScale sumRead ∧
                              Cont sumRead E ledgerRead ∧ Cont ledgerRead R readbackRead ∧
                                Cont readbackRead Z sealRead ∧
                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro leftUnary rightUnary ledgerUnary readbackUnary sealEndpointUnary sumRoute ledgerRoute
    readbackRoute sealRoute sealPkg
  have sumUnary : UnaryHistory sumRead :=
    unary_cont_closed leftUnary rightUnary sumRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed sumUnary ledgerUnary ledgerRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed ledgerReadUnary readbackUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary sealEndpointUnary sealRoute
  exact
    ⟨sumUnary, ledgerReadUnary, readbackReadUnary, sealReadUnary, sumRoute, ledgerRoute,
      readbackRoute, sealRoute, sealPkg⟩

end BEDC.Derived.RegularCauchyAffineCombinationUp
