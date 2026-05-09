import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

theorem CurvatureBracketCarrier_tensorial_section_transport
    {base fibre sec sec' tangentA tangentB derivativeA derivativeA' derivativeB derivativeB'
      provenance ledgerA ledgerA' ledgerB ledgerB' boundary boundary' curvatureLedger
      curvatureLedger' : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      ConnectionCarrierPacket base fibre sec' tangentA derivativeA' provenance ledgerA' ->
        ConnectionCarrierPacket base fibre sec' tangentB derivativeB' provenance ledgerB' ->
          hsame derivativeA derivativeA' ->
            hsame derivativeB derivativeB' ->
              Cont derivativeA' derivativeB' boundary' ->
                Cont boundary' provenance curvatureLedger' ->
                  CurvatureBracketCarrier base fibre sec' tangentA tangentB derivativeA'
                      derivativeB' provenance ledgerA' ledgerB' boundary' curvatureLedger' ∧
                    hsame boundary boundary' ∧ hsame curvatureLedger curvatureLedger' := by
  intro carrier packetA' packetB' sameDerivativeA sameDerivativeB boundaryCont' curvatureCont'
  have boundaryCont : Cont derivativeA derivativeB boundary :=
    carrier.right.right.left
  have curvatureCont : Cont boundary provenance curvatureLedger :=
    carrier.right.right.right
  have sameBoundary : hsame boundary boundary' :=
    cont_respects_hsame sameDerivativeA sameDerivativeB boundaryCont boundaryCont'
  have sameCurvatureLedger : hsame curvatureLedger curvatureLedger' :=
    cont_respects_hsame sameBoundary (hsame_refl provenance) curvatureCont curvatureCont'
  have transported :
      CurvatureBracketCarrier base fibre sec' tangentA tangentB derivativeA' derivativeB'
        provenance ledgerA' ledgerB' boundary' curvatureLedger' :=
    And.intro packetA' (And.intro packetB' (And.intro boundaryCont' curvatureCont'))
  exact And.intro transported (And.intro sameBoundary sameCurvatureLedger)

theorem CurvatureBracketCarrier_tensorial_transport_obligation
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger basePrime fibrePrime secPrime tangentAPrime tangentBPrime derivativeAPrime
      derivativeBPrime provenancePrime ledgerAPrime ledgerBPrime boundaryPrime
      curvatureLedgerPrime : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      ConnectionCarrierPacket basePrime fibrePrime secPrime tangentAPrime derivativeAPrime
          provenancePrime ledgerAPrime ->
        ConnectionCarrierPacket basePrime fibrePrime secPrime tangentBPrime derivativeBPrime
            provenancePrime ledgerBPrime ->
          hsame derivativeA derivativeAPrime ->
            hsame derivativeB derivativeBPrime ->
              hsame provenance provenancePrime ->
                Cont derivativeAPrime derivativeBPrime boundaryPrime ->
                  Cont boundaryPrime provenancePrime curvatureLedgerPrime ->
                    CurvatureBracketCarrier basePrime fibrePrime secPrime tangentAPrime
                        tangentBPrime derivativeAPrime derivativeBPrime provenancePrime ledgerAPrime
                        ledgerBPrime boundaryPrime curvatureLedgerPrime ∧
                      hsame boundary boundaryPrime ∧
                        hsame curvatureLedger curvatureLedgerPrime ∧
                          UnaryHistory boundaryPrime ∧ UnaryHistory curvatureLedgerPrime := by
  intro carrier packetA' packetB' sameDerivativeA sameDerivativeB sameProvenance
    boundaryCont' curvatureCont'
  have transported :=
    CurvatureBracketCarrier_tensorial_endpoint_transport carrier packetA' packetB'
      sameDerivativeA sameDerivativeB sameProvenance boundaryCont' curvatureCont'
  have rows :=
    CurvatureBracketCarrier_boundary_source_obligation transported.left
  exact And.intro transported.left
    (And.intro transported.right.left
      (And.intro transported.right.right
        (And.intro rows.left rows.right.left)))

end BEDC.Derived.CurvatureUp
