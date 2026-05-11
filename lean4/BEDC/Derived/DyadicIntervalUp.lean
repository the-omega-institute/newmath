import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicIntervalPacket [AskSetup] [PackageSetup]
    (left right width midpoint radius order provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory width ∧ UnaryHistory midpoint ∧
    UnaryHistory radius ∧ UnaryHistory order ∧ UnaryHistory provenance ∧
      UnaryHistory endpoint ∧ Cont left right width ∧ Cont left width midpoint ∧
        Cont right width radius ∧ Cont midpoint radius order ∧ Cont order provenance endpoint ∧
          PkgSig bundle endpoint pkg

theorem DyadicIntervalPacket_nested_refinement_ledger [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint left' right' width' midpoint'
      radius' order' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left right width midpoint radius order provenance endpoint bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          hsame provenance provenance' ->
            Cont left' right' width' ->
              Cont left' width' midpoint' ->
                Cont right' width' radius' ->
                  Cont midpoint' radius' order' ->
                    Cont order' provenance' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        DyadicIntervalPacket left' right' width' midpoint' radius' order'
                            provenance' endpoint' bundle pkg ∧
                          hsame width width' ∧ hsame midpoint midpoint' ∧ hsame radius radius' ∧
                            hsame order order' ∧ hsame endpoint endpoint' := by
  intro packet sameLeft sameRight sameProvenance widthRow' midpointRow' radiusRow'
    orderRow' endpointRow' pkgRow'
  obtain ⟨leftUnary, rightUnary, _widthUnary, _midpointUnary, _radiusUnary, _orderUnary,
    provenanceUnary, _endpointUnary, widthRow, midpointRow, radiusRow, orderRow, endpointRow,
    _pkgRow⟩ := packet
  have leftUnary' : UnaryHistory left' :=
    unary_transport leftUnary sameLeft
  have rightUnary' : UnaryHistory right' :=
    unary_transport rightUnary sameRight
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have widthUnary' : UnaryHistory width' :=
    unary_cont_closed leftUnary' rightUnary' widthRow'
  have midpointUnary' : UnaryHistory midpoint' :=
    unary_cont_closed leftUnary' widthUnary' midpointRow'
  have radiusUnary' : UnaryHistory radius' :=
    unary_cont_closed rightUnary' widthUnary' radiusRow'
  have orderUnary' : UnaryHistory order' :=
    unary_cont_closed midpointUnary' radiusUnary' orderRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed orderUnary' provenanceUnary' endpointRow'
  have sameWidth : hsame width width' :=
    cont_respects_hsame sameLeft sameRight widthRow widthRow'
  have sameMidpoint : hsame midpoint midpoint' :=
    cont_respects_hsame sameLeft sameWidth midpointRow midpointRow'
  have sameRadius : hsame radius radius' :=
    cont_respects_hsame sameRight sameWidth radiusRow radiusRow'
  have sameOrder : hsame order order' :=
    cont_respects_hsame sameMidpoint sameRadius orderRow orderRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameOrder sameProvenance endpointRow endpointRow'
  constructor
  · constructor
    · exact leftUnary'
    · constructor
      · exact rightUnary'
      · constructor
        · exact widthUnary'
        · constructor
          · exact midpointUnary'
          · constructor
            · exact radiusUnary'
            · constructor
              · exact orderUnary'
              · constructor
                · exact provenanceUnary'
                · constructor
                  · exact endpointUnary'
                  · constructor
                    · exact widthRow'
                    · constructor
                      · exact midpointRow'
                      · constructor
                        · exact radiusRow'
                        · constructor
                          · exact orderRow'
                          · constructor
                            · exact endpointRow'
                            · exact pkgRow'
  · constructor
    · exact sameWidth
    · constructor
      · exact sameMidpoint
      · constructor
        · exact sameRadius
        · constructor
          · exact sameOrder
          · exact sameEndpoint

theorem DyadicIntervalPacket_width_radius_ledger_exactness [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left right width midpoint radius order provenance endpoint bundle pkg ->
      UnaryHistory width ∧ UnaryHistory midpoint ∧ UnaryHistory radius ∧
        hsame midpoint (append left width) ∧ hsame radius (append right width) ∧
          hsame order (append midpoint radius) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  obtain ⟨_leftUnary, _rightUnary, widthUnary, midpointUnary, radiusUnary, _orderUnary,
    _provenanceUnary, _endpointUnary, _widthRow, midpointRow, radiusRow, orderRow,
    _endpointRow, pkgRow⟩ := packet
  exact
    And.intro widthUnary
      (And.intro midpointUnary
        (And.intro radiusUnary
          (And.intro midpointRow
            (And.intro radiusRow
              (And.intro orderRow pkgRow)))))

theorem DyadicIntervalPacket_real_seal_source_boundary [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint sealRowOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left right width midpoint radius order provenance endpoint bundle pkg ->
      Cont endpoint width sealRowOut ->
        PkgSig bundle sealRowOut pkg ->
          UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory radius ∧
            UnaryHistory width ∧ UnaryHistory order ∧ UnaryHistory sealRowOut ∧
              Cont endpoint width sealRowOut ∧ hsame sealRowOut (append endpoint width) ∧
                PkgSig bundle sealRowOut pkg := by
  intro packet sealRow sealPkg
  obtain ⟨leftUnary, rightUnary, widthUnary, _midpointUnary, radiusUnary, orderUnary,
    _provenanceUnary, endpointUnary, _widthRow, _midpointRow, _radiusRow, _orderRow,
    _endpointRow, _pkgRow⟩ := packet
  have sealUnary : UnaryHistory sealRowOut :=
    unary_cont_closed endpointUnary widthUnary sealRow
  exact
    And.intro leftUnary
      (And.intro rightUnary
        (And.intro radiusUnary
          (And.intro widthUnary
            (And.intro orderUnary
              (And.intro sealUnary
                (And.intro sealRow
                  (And.intro sealRow sealPkg)))))))

theorem DyadicIntervalPacket_endpoint_classifier_transport [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint left' right' width' midpoint'
      radius' order' provenance' endpoint' classifierRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left right width midpoint radius order provenance endpoint bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          hsame width width' ->
            hsame provenance provenance' ->
              Cont left' right' width' ->
                Cont left' width' midpoint' ->
                  Cont right' width' radius' ->
                    Cont midpoint' radius' order' ->
                      Cont order' provenance' endpoint' ->
                        Cont endpoint' width' classifierRow ->
                          PkgSig bundle endpoint' pkg ->
                            UnaryHistory classifierRow ∧ hsame endpoint endpoint' ∧
                              hsame classifierRow (append endpoint' width') := by
  intro packet sameLeft sameRight sameWidth sameProvenance widthRow' midpointRow' radiusRow'
    orderRow' endpointRow' classifierRowRow _classifierPkg
  obtain ⟨leftUnary, rightUnary, _widthUnary, _midpointUnary, _radiusUnary, _orderUnary,
    provenanceUnary, _endpointUnary, _widthRow, midpointRow, radiusRow, orderRow,
    endpointRow, _pkgRow⟩ := packet
  have leftUnary' : UnaryHistory left' :=
    unary_transport leftUnary sameLeft
  have rightUnary' : UnaryHistory right' :=
    unary_transport rightUnary sameRight
  have widthUnary' : UnaryHistory width' :=
    unary_cont_closed leftUnary' rightUnary' widthRow'
  have midpointUnary' : UnaryHistory midpoint' :=
    unary_cont_closed leftUnary' widthUnary' midpointRow'
  have radiusUnary' : UnaryHistory radius' :=
    unary_cont_closed rightUnary' widthUnary' radiusRow'
  have orderUnary' : UnaryHistory order' :=
    unary_cont_closed midpointUnary' radiusUnary' orderRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed orderUnary' provenanceUnary' endpointRow'
  have classifierUnary : UnaryHistory classifierRow :=
    unary_cont_closed endpointUnary' widthUnary' classifierRowRow
  have sameMidpoint : hsame midpoint midpoint' :=
    cont_respects_hsame sameLeft sameWidth midpointRow midpointRow'
  have sameRadius : hsame radius radius' :=
    cont_respects_hsame sameRight sameWidth radiusRow radiusRow'
  have sameOrder : hsame order order' :=
    cont_respects_hsame sameMidpoint sameRadius orderRow orderRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameOrder sameProvenance endpointRow endpointRow'
  exact And.intro classifierUnary (And.intro sameEndpoint classifierRowRow)
def DyadicIntervalEndpointPacket [AskSetup] [PackageSetup]
    (left right width order midpoint radius hsameLedger contLedger pkgrow nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hsameLedger ∧ UnaryHistory width ∧ Cont left right order ∧
    Cont left right midpoint ∧ Cont midpoint width radius ∧ Cont order radius contLedger ∧
      Cont contLedger pkgrow nameRow ∧ PkgSig bundle pkgrow pkg

theorem DyadicIntervalPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint leftE rightE widthE orderE
      midpointE radiusE hsameLedger contLedger pkgrow nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left right width midpoint radius order provenance endpoint bundle pkg ->
      DyadicIntervalEndpointPacket leftE rightE widthE orderE midpointE radiusE hsameLedger
        contLedger pkgrow nameRow bundle pkg ->
        UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory width ∧ UnaryHistory midpoint ∧
          UnaryHistory radius ∧ UnaryHistory order ∧ UnaryHistory endpoint ∧
            Cont left right width ∧ Cont left width midpoint ∧ Cont right width radius ∧
              Cont midpoint radius order ∧ Cont order provenance endpoint ∧
                UnaryHistory hsameLedger ∧ Cont leftE rightE orderE ∧
                  Cont leftE rightE midpointE ∧ Cont midpointE widthE radiusE ∧
                    Cont contLedger pkgrow nameRow ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle pkgrow pkg := by
  intro packet endpointPacket
  obtain ⟨leftUnary, rightUnary, widthUnary, midpointUnary, radiusUnary, orderUnary,
    provenanceUnary, _endpointUnary, widthRow, midpointRow, radiusRow, orderRow, endpointRow,
    endpointPkg⟩ := packet
  obtain ⟨hsameLedgerUnary, _widthEUnary, orderERow, midpointERow, radiusERow,
    _contLedgerRow, nameRowRow, pkgrowPkg⟩ := endpointPacket
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed orderUnary provenanceUnary endpointRow
  exact
    And.intro leftUnary
      (And.intro rightUnary
        (And.intro widthUnary
          (And.intro midpointUnary
            (And.intro radiusUnary
              (And.intro orderUnary
                (And.intro endpointUnary
                  (And.intro widthRow
                    (And.intro midpointRow
                      (And.intro radiusRow
                        (And.intro orderRow
                          (And.intro endpointRow
                            (And.intro hsameLedgerUnary
                              (And.intro orderERow
                                (And.intro midpointERow
                                  (And.intro radiusERow
                                    (And.intro nameRowRow
                                      (And.intro endpointPkg pkgrowPkg)))))))))))))))))

theorem DyadicIntervalEndpointPacket_nested_refinement_ledger [AskSetup] [PackageSetup]
    {left right width order midpoint radius hsameLedger contLedger pkgrow nameRow left' right'
      width' order' midpoint' radius' contLedger' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalEndpointPacket left right width order midpoint radius hsameLedger
        contLedger pkgrow nameRow bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          hsame width width' ->
            Cont left' right' order' ->
              Cont left' right' midpoint' ->
                Cont midpoint' width' radius' ->
                  Cont order' radius' contLedger' ->
                    Cont contLedger' pkgrow nameRow' ->
                      PkgSig bundle pkgrow pkg ->
                        DyadicIntervalEndpointPacket left' right' width' order' midpoint'
                            radius' hsameLedger contLedger' pkgrow nameRow' bundle pkg ∧
                          hsame order order' ∧
                            hsame midpoint midpoint' ∧
                              hsame radius radius' ∧ hsame nameRow nameRow' := by
  intro packet sameLeft sameRight sameWidth orderCont' midpointCont' radiusCont'
    contLedgerCont' nameRowCont' pkgSig'
  have sameOrder : hsame order order' :=
    cont_respects_hsame sameLeft sameRight packet.right.right.left orderCont'
  have sameMidpoint : hsame midpoint midpoint' :=
    cont_respects_hsame sameLeft sameRight packet.right.right.right.left midpointCont'
  have sameRadius : hsame radius radius' :=
    cont_respects_hsame sameMidpoint sameWidth packet.right.right.right.right.left radiusCont'
  have sameContLedger : hsame contLedger contLedger' :=
    cont_respects_hsame sameOrder sameRadius packet.right.right.right.right.right.left
      contLedgerCont'
  have sameNameRow : hsame nameRow nameRow' :=
    cont_respects_hsame sameContLedger (hsame_refl pkgrow)
      packet.right.right.right.right.right.right.left nameRowCont'
  have widthUnary' : UnaryHistory width' :=
    unary_transport packet.right.left sameWidth
  exact
    And.intro
      (And.intro packet.left
        (And.intro widthUnary'
          (And.intro orderCont'
            (And.intro midpointCont'
              (And.intro radiusCont'
                (And.intro contLedgerCont'
                  (And.intro nameRowCont' pkgSig')))))))
      (And.intro sameOrder
        (And.intro sameMidpoint
          (And.intro sameRadius sameNameRow)))

theorem DyadicIntervalEndpointPacket_endpoint_classifier_transport [AskSetup] [PackageSetup]
    {left right width order midpoint radius hsameLedger contLedger pkgrow nameRow left' right'
      width' order' midpoint' radius' contLedger' nameRow' endpointWitness endpointWitness' :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalEndpointPacket left right width order midpoint radius hsameLedger
        contLedger pkgrow nameRow bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          hsame width width' ->
            Cont left' right' order' ->
              Cont left' right' midpoint' ->
                Cont midpoint' width' radius' ->
                  Cont order' radius' contLedger' ->
                    Cont contLedger' pkgrow nameRow' ->
                      PkgSig bundle pkgrow pkg ->
                        Cont nameRow width endpointWitness ->
                          Cont nameRow' width' endpointWitness' ->
                            DyadicIntervalEndpointPacket left' right' width' order' midpoint'
                                radius' hsameLedger contLedger' pkgrow nameRow' bundle pkg ∧
                              hsame endpointWitness endpointWitness' ∧
                                PkgSig bundle pkgrow pkg := by
  intro packet sameLeft sameRight sameWidth orderCont' midpointCont' radiusCont'
    contLedgerCont' nameRowCont' pkgSig' endpointWitnessRow endpointWitnessRow'
  have transported :=
    DyadicIntervalEndpointPacket_nested_refinement_ledger packet sameLeft sameRight sameWidth
      orderCont' midpointCont' radiusCont' contLedgerCont' nameRowCont' pkgSig'
  have sameNameRow : hsame nameRow nameRow' :=
    transported.right.right.right.right
  have sameEndpointWitness : hsame endpointWitness endpointWitness' :=
    cont_respects_hsame sameNameRow sameWidth endpointWitnessRow endpointWitnessRow'
  exact
    And.intro transported.left
      (And.intro sameEndpointWitness pkgSig')

end BEDC.Derived.DyadicIntervalUp
