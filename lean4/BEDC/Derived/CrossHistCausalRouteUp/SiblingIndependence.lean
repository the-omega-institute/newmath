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
open BEDC.GroundCompiler.EventFlow

theorem CrossHistCausalRouteCarrier_sibling_independence
    (x : CrossHistCausalRouteUp) :
    ∃ observerA observerB causalRows maxRate symmetryGate nonEscapeGate trace transport
      access provenance localName : BHist,
      crossHistCausalRouteFields x =
          [observerA, observerB, causalRows, maxRate, symmetryGate, nonEscapeGate,
            trace, transport, access, provenance, localName] ∧
        crossHistCausalRouteToEventFlow x =
          [[BMark.b0],
            crossHistCausalRouteEncodeBHist observerA,
            [BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist observerB,
            [BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist causalRows,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist maxRate,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist symmetryGate,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist nonEscapeGate,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0],
            crossHistCausalRouteEncodeBHist trace,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist transport,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist access,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist provenance,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist localName] ∧
          List.Mem (crossHistCausalRouteEncodeBHist causalRows)
            (crossHistCausalRouteToEventFlow x) ∧
            List.Mem (crossHistCausalRouteEncodeBHist maxRate)
              (crossHistCausalRouteToEventFlow x) ∧
              List.Mem (crossHistCausalRouteEncodeBHist trace)
                (crossHistCausalRouteToEventFlow x) ∧
                crossHistCausalRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  cases x with
  | mk observerA observerB causalRows maxRate symmetryGate nonEscapeGate trace transport
      access provenance localName =>
      refine
        ⟨observerA, observerB, causalRows, maxRate, symmetryGate, nonEscapeGate,
          trace, transport, access, provenance, localName, rfl, rfl, ?_, ?_, ?_, rfl⟩
      · exact
          List.Mem.tail [BMark.b0] <|
            List.Mem.tail (crossHistCausalRouteEncodeBHist observerA) <|
              List.Mem.tail [BMark.b1, BMark.b0] <|
                List.Mem.tail (crossHistCausalRouteEncodeBHist observerB) <|
                  List.Mem.tail [BMark.b1, BMark.b1, BMark.b0] (List.Mem.head _)
      · exact
          List.Mem.tail [BMark.b0] <|
            List.Mem.tail (crossHistCausalRouteEncodeBHist observerA) <|
              List.Mem.tail [BMark.b1, BMark.b0] <|
                List.Mem.tail (crossHistCausalRouteEncodeBHist observerB) <|
                  List.Mem.tail [BMark.b1, BMark.b1, BMark.b0] <|
                    List.Mem.tail (crossHistCausalRouteEncodeBHist causalRows) <|
                      List.Mem.tail [BMark.b1, BMark.b1, BMark.b1, BMark.b0]
                        (List.Mem.head _)
      · exact
          List.Mem.tail [BMark.b0] <|
            List.Mem.tail (crossHistCausalRouteEncodeBHist observerA) <|
              List.Mem.tail [BMark.b1, BMark.b0] <|
                List.Mem.tail (crossHistCausalRouteEncodeBHist observerB) <|
                  List.Mem.tail [BMark.b1, BMark.b1, BMark.b0] <|
                    List.Mem.tail (crossHistCausalRouteEncodeBHist causalRows) <|
                      List.Mem.tail [BMark.b1, BMark.b1, BMark.b1, BMark.b0] <|
                        List.Mem.tail (crossHistCausalRouteEncodeBHist maxRate) <|
                          List.Mem.tail
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0] <|
                            List.Mem.tail
                              (crossHistCausalRouteEncodeBHist symmetryGate) <|
                              List.Mem.tail
                                [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                                  BMark.b0] <|
                                List.Mem.tail
                                  (crossHistCausalRouteEncodeBHist nonEscapeGate) <|
                                  List.Mem.tail
                                    [BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                                      BMark.b1, BMark.b1, BMark.b0]
                                    (List.Mem.head _)

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
