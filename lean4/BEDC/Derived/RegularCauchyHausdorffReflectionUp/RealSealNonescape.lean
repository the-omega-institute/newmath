import BEDC.Derived.RegularCauchyHausdorffReflectionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyHausdorffReflectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyHausdorffReflectionCarrier_real_seal_nonescape
    [AskSetup] [PackageSetup]
    {X Y S T D U E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X S D ->
      Cont Y T U ->
        Cont D U E ->
          Cont E N sealRead ->
            UnaryHistory X ->
              UnaryHistory S ->
                UnaryHistory D ->
                  UnaryHistory U ->
                    UnaryHistory E ->
                      UnaryHistory N ->
                        PkgSig bundle sealRead pkg ->
                          UnaryHistory sealRead ∧ Cont X S D ∧ Cont Y T U ∧
                            Cont D U E ∧ Cont E N sealRead ∧
                              PkgSig bundle sealRead pkg ∧
                                List.Mem (regularCauchyHausdorffReflectionEncodeBHist E)
                                  (regularCauchyHausdorffReflectionToEventFlow
                                    (RegularCauchyHausdorffReflectionUp.mk
                                      X Y S T D U E H C P N)) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro routeXS routeYT routeDU routeEN _unaryX _unaryS _unaryD _unaryU unaryE
    unaryN sealPkg
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed unaryE unaryN routeEN
  exact
    ⟨sealUnary, routeXS, routeYT, routeDU, routeEN, sealPkg,
      by
        simp only [regularCauchyHausdorffReflectionToEventFlow,
          regularCauchyHausdorffReflectionFields, List.map_cons]
        right
        right
        right
        right
        right
        right
        left⟩

end BEDC.Derived.RegularCauchyHausdorffReflectionUp
