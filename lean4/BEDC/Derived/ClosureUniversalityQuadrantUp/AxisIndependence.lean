import BEDC.Derived.ClosureUniversalityQuadrantUp.TasteGate

namespace BEDC.Derived.ClosureUniversalityQuadrantUp

open BEDC.FKernel.Hist

def closureUniversalityQuadrantFields :
    ClosureUniversalityQuadrantUp → List BHist
  -- BEDC touchpoint anchor: ClosureUniversalityQuadrantUp BHist
  | ClosureUniversalityQuadrantUp.mk universality closure tag substrate anchors transport
      routes provenance nameCert =>
      [universality, closure, tag, substrate, anchors, transport, routes, provenance,
        nameCert]

theorem ClosureUniversalityQuadrantCarrier_axis_independence_boundary
    {universality closure tag substrate anchors transport routes provenance nameCert : BHist} :
    closureUniversalityQuadrantFields
        (ClosureUniversalityQuadrantUp.mk universality closure tag substrate anchors transport
          routes provenance nameCert) =
      [universality, closure, tag, substrate, anchors, transport, routes, provenance,
        nameCert] ∧
      (closureUniversalityQuadrantToEventFlow
            (ClosureUniversalityQuadrantUp.mk universality closure tag substrate anchors
              transport routes provenance nameCert) =
          closureUniversalityQuadrantToEventFlow
            (ClosureUniversalityQuadrantUp.mk closure universality tag substrate anchors
              transport routes provenance nameCert) →
        universality = closure) := by
  -- BEDC touchpoint anchor: ClosureUniversalityQuadrantUp BHist
  constructor
  · rfl
  · intro sameFlow
    have sameCarrier :
        ClosureUniversalityQuadrantUp.mk universality closure tag substrate anchors
            transport routes provenance nameCert =
          ClosureUniversalityQuadrantUp.mk closure universality tag substrate anchors
            transport routes provenance nameCert :=
      closureUniversalityQuadrantToEventFlow_injective sameFlow
    injection sameCarrier

end BEDC.Derived.ClosureUniversalityQuadrantUp
