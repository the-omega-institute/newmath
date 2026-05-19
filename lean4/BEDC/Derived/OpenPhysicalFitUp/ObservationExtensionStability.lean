import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OpenPhysicalFitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem OpenPhysicalFit_observation_extension_stability [AskSetup] [PackageSetup]
    {E C L F extensionRead ledgerRead refutationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E ->
      UnaryHistory C ->
        UnaryHistory L ->
          UnaryHistory F ->
            Cont E C extensionRead ->
              Cont extensionRead L ledgerRead ->
                Cont F C refutationRead ->
                  PkgSig bundle ledgerRead pkg ->
                    PkgSig bundle refutationRead pkg ->
                      UnaryHistory extensionRead ∧
                        UnaryHistory ledgerRead ∧
                          UnaryHistory refutationRead ∧
                            Cont E C extensionRead ∧
                              Cont extensionRead L ledgerRead ∧
                                Cont F C refutationRead ∧
                                  PkgSig bundle ledgerRead pkg ∧
                                    PkgSig bundle refutationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro eUnary cUnary lUnary fUnary extensionRoute ledgerRoute refutationRoute ledgerPkg
    refutationPkg
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed eUnary cUnary extensionRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed extensionUnary lUnary ledgerRoute
  have refutationUnary : UnaryHistory refutationRead :=
    unary_cont_closed fUnary cUnary refutationRoute
  exact
    ⟨extensionUnary, ledgerUnary, refutationUnary, extensionRoute, ledgerRoute,
      refutationRoute, ledgerPkg, refutationPkg⟩

end BEDC.Derived.OpenPhysicalFitUp
