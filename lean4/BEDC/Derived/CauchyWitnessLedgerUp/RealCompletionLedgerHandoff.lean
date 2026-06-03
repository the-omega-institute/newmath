import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyWitnessLedgerRealCompletionHandoff
    [AskSetup] [PackageSetup]
    {Q B S K H C P N route sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q →
      UnaryHistory B →
        UnaryHistory S →
          UnaryHistory K →
            PkgSig bundle P pkg →
              Cont Q B route →
                Cont route S sealRead →
                  PkgSig bundle sealRead pkg →
                    UnaryHistory Q ∧ UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory K ∧
                      UnaryHistory route ∧ UnaryHistory sealRead ∧ Cont Q B route ∧
                        Cont route S sealRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro unaryQ unaryB unaryS unaryK provenancePkg routeCont sealCont sealPkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed unaryQ unaryB routeCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed routeUnary unaryS sealCont
  exact
    ⟨unaryQ, unaryB, unaryS, unaryK, routeUnary, sealUnary, routeCont, sealCont,
      provenancePkg, sealPkg⟩

end BEDC.Derived.CauchyWitnessLedgerUp
