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

theorem CurvatureBracketCarrier_tensorial_section_change_row
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger section' derivativeA' derivativeB' ledgerA' ledgerB' boundary'
      curvatureLedger' : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      hsame sec section' ->
        Cont section' tangentA derivativeA' ->
          Cont derivativeA' provenance ledgerA' ->
            Cont section' tangentB derivativeB' ->
              Cont derivativeB' provenance ledgerB' ->
                Cont derivativeA' derivativeB' boundary' ->
                  Cont boundary' provenance curvatureLedger' ->
                    CurvatureBracketCarrier base fibre section' tangentA tangentB derivativeA'
                        derivativeB' provenance ledgerA' ledgerB' boundary' curvatureLedger' ∧
                      hsame derivativeA derivativeA' ∧ hsame derivativeB derivativeB' ∧
                        hsame boundary boundary' ∧ hsame curvatureLedger curvatureLedger' := by
  intro carrier sameSection derivativeACont' ledgerACont' derivativeBCont' ledgerBCont'
    boundaryCont' curvatureCont'
  have packetA : ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA :=
    carrier.left
  have packetB : ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB :=
    carrier.right.left
  have secCont : Cont base fibre sec :=
    packetA.right.right.right.right.left
  have secCont' : Cont base fibre section' :=
    cont_result_hsame_transport secCont sameSection
  have packetA' :
      ConnectionCarrierPacket base fibre section' tangentA derivativeA' provenance ledgerA' :=
    And.intro packetA.left
      (And.intro packetA.right.left
        (And.intro packetA.right.right.left
          (And.intro packetA.right.right.right.left
            (And.intro secCont' (And.intro derivativeACont' ledgerACont')))))
  have packetB' :
      ConnectionCarrierPacket base fibre section' tangentB derivativeB' provenance ledgerB' :=
    And.intro packetB.left
      (And.intro packetB.right.left
        (And.intro packetB.right.right.left
          (And.intro packetB.right.right.right.left
            (And.intro secCont' (And.intro derivativeBCont' ledgerBCont')))))
  have sameDerivativeA : hsame derivativeA derivativeA' :=
    cont_respects_hsame sameSection (hsame_refl tangentA)
      packetA.right.right.right.right.right.left derivativeACont'
  have sameDerivativeB : hsame derivativeB derivativeB' :=
    cont_respects_hsame sameSection (hsame_refl tangentB)
      packetB.right.right.right.right.right.left derivativeBCont'
  have transported :=
    CurvatureBracketCarrier_tensorial_endpoint_transport carrier packetA' packetB'
      sameDerivativeA sameDerivativeB (hsame_refl provenance) boundaryCont' curvatureCont'
  exact And.intro transported.left
    (And.intro sameDerivativeA
      (And.intro sameDerivativeB
        (And.intro transported.right.left transported.right.right)))

end BEDC.Derived.CurvatureUp
