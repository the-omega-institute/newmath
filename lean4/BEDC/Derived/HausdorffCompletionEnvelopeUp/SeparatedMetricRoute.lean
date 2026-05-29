import BEDC.Derived.HausdorffCompletionEnvelopeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HausdorffCompletionEnvelopeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffCompletionEnvelopeCarrier_separated_metric_route [AskSetup] [PackageSetup]
    {H S M W D R L T K P N metricRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont H S M ->
      Cont M W D ->
        Cont D R L ->
          Cont L K realRead ->
            UnaryHistory H ->
              UnaryHistory S ->
                UnaryHistory M ->
                  UnaryHistory W ->
                    UnaryHistory D ->
                      UnaryHistory R ->
                        UnaryHistory L ->
                          UnaryHistory K ->
                            PkgSig bundle realRead pkg ->
                              UnaryHistory realRead ∧ Cont H S M ∧ Cont M W D ∧
                                Cont D R L ∧ Cont L K realRead ∧
                                  PkgSig bundle realRead pkg ∧
                                    List.Mem (hausdorffCompletionEnvelopeEncodeBHist H)
                                      (hausdorffCompletionEnvelopeToEventFlow
                                        (HausdorffCompletionEnvelopeUp.mk
                                          H S M W D R L T K P N)) ∧
                                      List.Mem (hausdorffCompletionEnvelopeEncodeBHist L)
                                        (hausdorffCompletionEnvelopeToEventFlow
                                          (HausdorffCompletionEnvelopeUp.mk
                                            H S M W D R L T K P N)) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro routeHS routeMW routeDR routeLK _unaryH _unaryS _unaryM _unaryW _unaryD
    _unaryR unaryL unaryK realPkg
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed unaryL unaryK routeLK
  exact
    ⟨realUnary, routeHS, routeMW, routeDR, routeLK, realPkg,
      by
        simp only [hausdorffCompletionEnvelopeToEventFlow, hausdorffCompletionEnvelopeFields,
          List.map_cons]
        left,
      by
        simp only [hausdorffCompletionEnvelopeToEventFlow, hausdorffCompletionEnvelopeFields,
          List.map_cons]
        right
        right
        right
        right
        right
        right
        left⟩

end BEDC.Derived.HausdorffCompletionEnvelopeUp
