import BEDC.Derived.CriticalLineWitnessUp.ComponentwiseStdbridgeTransport
import BEDC.Derived.CriticalLineWitnessUp.RootRefusalBoundaryTotality

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_boundary_stdbridge_nonescape
    {Z S M R Q H C P N zetaStripRead refusalRead rhBoundary consumerRead imageRead
      readbackRead bridgeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaStripRead ->
        Cont N Q refusalRead ->
          Cont zetaStripRead refusalRead rhBoundary ->
            Cont rhBoundary C consumerRead ->
              Cont Z S imageRead ->
                Cont imageRead H readbackRead ->
                  Cont readbackRead N bridgeRead ->
                    SemanticNameCert
                        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row consumerRead ∧ Cont Z S zetaStripRead ∧
                            Cont N Q refusalRead)
                        (fun row : BHist =>
                          hsame row consumerRead ∧ Cont rhBoundary C consumerRead)
                        hsame ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row Z ∨ hsame row S ∨ hsame row imageRead ∨
                            hsame row readbackRead ∨ hsame row bridgeRead)
                        (fun row : BHist =>
                          hsame row bridgeRead ∧ Cont readbackRead N bridgeRead)
                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaStripRoute refusalRoute boundaryRoute consumerRoute imageRoute
    readbackRoute bridgeRoute
  have refusalBoundary :=
    CriticalLineWitnessCarrier_root_refusal_boundary_totality
      packet zetaStripRoute refusalRoute boundaryRoute consumerRoute
  have stdbridge :=
    CriticalLineWitnessCarrier_componentwise_stdbridge_transport
      packet imageRoute readbackRoute bridgeRoute
  exact And.intro refusalBoundary.left stdbridge.left

end BEDC.Derived.CriticalLineWitnessUp
