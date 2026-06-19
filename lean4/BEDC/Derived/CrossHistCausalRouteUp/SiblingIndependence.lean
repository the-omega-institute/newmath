import BEDC.Derived.CrossHistCausalRouteUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CrossHistCausalRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CrossHistCausalRoute_sibling_independence [AskSetup] [PackageSetup]
    {observerA observerB causalRoute maxRate observerSource observerGate continuation transport
      accessRoutes provenance localName routeRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory observerA -> UnaryHistory observerB -> UnaryHistory maxRate ->
      UnaryHistory observerSource -> UnaryHistory observerGate -> UnaryHistory localName ->
        Cont observerA observerB causalRoute -> Cont causalRoute maxRate continuation ->
          Cont observerSource observerGate accessRoutes -> Cont continuation localName routeRead ->
            PkgSig bundle provenance pkg ->
              UnaryHistory causalRoute ∧ UnaryHistory continuation ∧ UnaryHistory accessRoutes ∧
                UnaryHistory routeRead ∧
                List.Mem (crossHistCausalRouteEncodeBHist observerA)
                  (crossHistCausalRouteToEventFlow
                    (CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate
                      observerSource observerGate continuation transport accessRoutes provenance
                      localName)) ∧
                List.Mem (crossHistCausalRouteEncodeBHist causalRoute)
                  (crossHistCausalRouteToEventFlow
                    (CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate
                      observerSource observerGate continuation transport accessRoutes provenance
                      localName)) ∧
                List.Mem (crossHistCausalRouteEncodeBHist maxRate)
                  (crossHistCausalRouteToEventFlow
                    (CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate
                      observerSource observerGate continuation transport accessRoutes provenance
                      localName)) ∧
                List.Mem (crossHistCausalRouteEncodeBHist observerGate)
                  (crossHistCausalRouteToEventFlow
                    (CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate
                      observerSource observerGate continuation transport accessRoutes provenance
                      localName)) ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig List.Mem
  intro observerAUnary observerBUnary maxRateUnary observerSourceUnary observerGateUnary
    localNameUnary observerRoute continuationRoute accessRoute routeReadRoute provenancePkg
  have causalRouteUnary : UnaryHistory causalRoute :=
    unary_cont_closed observerAUnary observerBUnary observerRoute
  have continuationUnary : UnaryHistory continuation :=
    unary_cont_closed causalRouteUnary maxRateUnary continuationRoute
  have accessRoutesUnary : UnaryHistory accessRoutes :=
    unary_cont_closed observerSourceUnary observerGateUnary accessRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed continuationUnary localNameUnary routeReadRoute
  have observerAListed :
      List.Mem (crossHistCausalRouteEncodeBHist observerA)
        (crossHistCausalRouteToEventFlow
          (CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate
            observerSource observerGate continuation transport accessRoutes provenance
            localName)) := by
    change
      List.Mem (crossHistCausalRouteEncodeBHist observerA)
        [[BMark.b0], crossHistCausalRouteEncodeBHist observerA, [BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerB,
          [BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist causalRoute,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist maxRate,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerSource,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerGate,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          crossHistCausalRouteEncodeBHist continuation,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist accessRoutes,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist localName]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have causalRouteListed :
      List.Mem (crossHistCausalRouteEncodeBHist causalRoute)
        (crossHistCausalRouteToEventFlow
          (CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate
            observerSource observerGate continuation transport accessRoutes provenance
            localName)) := by
    change
      List.Mem (crossHistCausalRouteEncodeBHist causalRoute)
        [[BMark.b0], crossHistCausalRouteEncodeBHist observerA, [BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerB,
          [BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist causalRoute,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist maxRate,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerSource,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerGate,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          crossHistCausalRouteEncodeBHist continuation,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist accessRoutes,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist localName]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))))
  have maxRateListed :
      List.Mem (crossHistCausalRouteEncodeBHist maxRate)
        (crossHistCausalRouteToEventFlow
          (CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate
            observerSource observerGate continuation transport accessRoutes provenance
            localName)) := by
    change
      List.Mem (crossHistCausalRouteEncodeBHist maxRate)
        [[BMark.b0], crossHistCausalRouteEncodeBHist observerA, [BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerB,
          [BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist causalRoute,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist maxRate,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerSource,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerGate,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          crossHistCausalRouteEncodeBHist continuation,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist accessRoutes,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist localName]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ List.mem_cons_self))))))
  have observerGateListed :
      List.Mem (crossHistCausalRouteEncodeBHist observerGate)
        (crossHistCausalRouteToEventFlow
          (CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate
            observerSource observerGate continuation transport accessRoutes provenance
            localName)) := by
    change
      List.Mem (crossHistCausalRouteEncodeBHist observerGate)
        [[BMark.b0], crossHistCausalRouteEncodeBHist observerA, [BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerB,
          [BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist causalRoute,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist maxRate,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerSource,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist observerGate,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          crossHistCausalRouteEncodeBHist continuation,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist accessRoutes,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          crossHistCausalRouteEncodeBHist localName]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _
                        (List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _ List.mem_cons_self))))))))))
  exact
    ⟨causalRouteUnary, continuationUnary, accessRoutesUnary, routeReadUnary,
      observerAListed, causalRouteListed, maxRateListed, observerGateListed, provenancePkg⟩

end BEDC.Derived.CrossHistCausalRouteUp
