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

theorem HausdorffCompletionEnvelopeCarrier_sibling_route [AskSetup] [PackageSetup]
    {H S M W D R L T K P N separatedRead completionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont H S separatedRead →
      Cont separatedRead M completionRead →
        Cont R K realRead →
          UnaryHistory H →
            UnaryHistory S →
              UnaryHistory M →
                UnaryHistory R →
                  UnaryHistory K →
                    PkgSig bundle realRead pkg →
                      UnaryHistory separatedRead ∧ UnaryHistory completionRead ∧
                        UnaryHistory realRead ∧
                          List.Mem (hausdorffCompletionEnvelopeEncodeBHist K)
                            (hausdorffCompletionEnvelopeToEventFlow
                              (HausdorffCompletionEnvelopeUp.mk
                                H S M W D R L T K P N)) ∧
                            List.Mem (hausdorffCompletionEnvelopeEncodeBHist N)
                              (hausdorffCompletionEnvelopeToEventFlow
                                (HausdorffCompletionEnvelopeUp.mk
                                  H S M W D R L T K P N)) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro separatedRoute completionRoute realRoute unaryH unaryS unaryM unaryR unaryK _realPkg
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed unaryH unaryS separatedRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed separatedUnary unaryM completionRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed unaryR unaryK realRoute
  exact
    ⟨separatedUnary, completionUnary, realUnary,
      by
        simp only [hausdorffCompletionEnvelopeToEventFlow, hausdorffCompletionEnvelopeFields,
          List.map_cons]
        right
        right
        right
        right
        right
        right
        right
        right
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
        right
        right
        right
        right
        left⟩

end BEDC.Derived.HausdorffCompletionEnvelopeUp
