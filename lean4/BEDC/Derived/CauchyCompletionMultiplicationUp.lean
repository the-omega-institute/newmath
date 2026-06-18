import BEDC.Derived.CauchyCompletionMultiplicationUp.TasteGate
import BEDC.FKernel.Cont.Assoc

namespace BEDC.Derived.CauchyCompletionMultiplicationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CauchyCompletionMultiplication_flattening_route
    {M O I A S R D E MO MOI MOIA SR SRD publicFace flattened : BHist}
    (monadOuter : Cont M O MO)
    (idempotenceRoute : Cont MO I MOI)
    (associativityRoute : Cont MOI A MOIA)
    (streamReadback : Cont S R SR)
    (dyadicRoute : Cont SR D SRD)
    (realSealRoute : Cont SRD E publicFace)
    (flattenedRoute : Cont MOIA publicFace flattened) :
    Cont M (append O (append I (append A publicFace))) flattened ∧
      Cont S (append R (append D E)) publicFace := by
  -- BEDC touchpoint anchor: BHist Cont append
  constructor
  · cases monadOuter
    cases idempotenceRoute
    cases associativityRoute
    cases flattenedRoute
    exact
      (append_assoc (append (append M O) I) A publicFace).trans
        ((append_assoc (append M O) I (append A publicFace)).trans
          (append_assoc M O (append I (append A publicFace))))
  · cases streamReadback
    cases dyadicRoute
    cases realSealRoute
    exact
      (append_assoc (append S R) D E).trans
        (append_assoc S R (append D E))

end BEDC.Derived.CauchyCompletionMultiplicationUp
