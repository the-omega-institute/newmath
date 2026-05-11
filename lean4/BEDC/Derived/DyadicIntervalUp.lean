import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem DyadicIntervalPacket_refined_width_radius_transport [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left right width midpoint radius order provenance endpoint bundle pkg ->
      Cont endpoint width sealRow ->
        hsame width radius ->
          hsame sealRow (append endpoint radius) := by
  intro packet sealRowCont widthRadius
  obtain ⟨_leftUnary, _rightUnary, widthUnary, _midpointUnary, _radiusUnary, _orderUnary,
    _provenanceUnary, endpointUnary, _widthRow, _midpointRow, _radiusRow, _orderRow,
    _endpointRow, _pkgRow⟩ := packet
  have radiusEndpoint : Cont endpoint radius (append endpoint radius) := by
    rfl
  have _sealUnary : UnaryHistory sealRow :=
    unary_cont_closed endpointUnary widthUnary sealRowCont
  exact cont_respects_hsame (hsame_refl endpoint) widthRadius sealRowCont radiusEndpoint

theorem DyadicIntervalPacket_scoped_dependency_package [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint sealRowOut windowRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left right width midpoint radius order provenance endpoint bundle pkg ->
      Cont endpoint width sealRowOut ->
        Cont sealRowOut radius windowRow ->
          PkgSig bundle windowRow pkg ->
            UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory width ∧
              UnaryHistory radius ∧ UnaryHistory sealRowOut ∧ UnaryHistory windowRow ∧
                Cont endpoint width sealRowOut ∧ Cont sealRowOut radius windowRow ∧
                  hsame sealRowOut (append endpoint width) ∧
                    hsame windowRow (append sealRowOut radius) ∧
                      PkgSig bundle windowRow pkg := by
  intro packet sealRow windowCont windowPkg
  obtain ⟨leftUnary, rightUnary, widthUnary, _midpointUnary, radiusUnary, _orderUnary,
    _provenanceUnary, endpointUnary, _widthRow, _midpointRow, _radiusRow, _orderRow,
    _endpointRow, _pkgRow⟩ := packet
  have sealUnary : UnaryHistory sealRowOut :=
    unary_cont_closed endpointUnary widthUnary sealRow
  have windowUnary : UnaryHistory windowRow :=
    unary_cont_closed sealUnary radiusUnary windowCont
  exact
    And.intro leftUnary
      (And.intro rightUnary
        (And.intro widthUnary
          (And.intro radiusUnary
            (And.intro sealUnary
              (And.intro windowUnary
                  (And.intro sealRow
                    (And.intro windowCont
                      (And.intro sealRow
                        (And.intro windowCont windowPkg)))))))))

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

theorem DyadicIntervalPacket_regular_window_seal_handoff [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint windowSource sealRowOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left right width midpoint radius order provenance endpoint bundle pkg ->
      Cont endpoint radius windowSource ->
        Cont windowSource width sealRowOut ->
          PkgSig bundle sealRowOut pkg ->
            UnaryHistory windowSource ∧ UnaryHistory sealRowOut ∧
              hsame windowSource (append endpoint radius) ∧
                hsame sealRowOut (append windowSource width) ∧
                  Cont endpoint radius windowSource ∧ Cont windowSource width sealRowOut ∧
                    PkgSig bundle sealRowOut pkg := by
  intro packet windowRow sealRow sealPkg
  obtain ⟨_leftUnary, _rightUnary, widthUnary, _midpointUnary, radiusUnary, _orderUnary,
    _provenanceUnary, endpointUnary, _widthRow, _midpointRow, _radiusRow, _orderRow,
    _endpointRow, _pkgRow⟩ := packet
  have windowUnary : UnaryHistory windowSource :=
    unary_cont_closed endpointUnary radiusUnary windowRow
  have sealUnary : UnaryHistory sealRowOut :=
    unary_cont_closed windowUnary widthUnary sealRow
  exact
    And.intro windowUnary
      (And.intro sealUnary
        (And.intro windowRow
          (And.intro sealRow
            (And.intro windowRow
              (And.intro sealRow sealPkg)))))

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

theorem DyadicIntervalPacket_refined_width_enclosure_package [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint left' right' width' midpoint'
      radius' order' provenance' endpoint' sealRow windowRow : BHist}
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
                        Cont endpoint' width' sealRow ->
                          Cont sealRow radius' windowRow ->
                            PkgSig bundle windowRow pkg ->
                              DyadicIntervalPacket left' right' width' midpoint' radius' order'
                                  provenance' endpoint' bundle pkg ∧
                                UnaryHistory sealRow ∧
                                  UnaryHistory windowRow ∧
                                    hsame width width' ∧
                                      hsame radius radius' ∧
                                        PkgSig bundle windowRow pkg := by
  intro packet sameLeft sameRight sameProvenance widthRow' midpointRow' radiusRow' orderRow'
    endpointRow' endpointPkg sealCont windowCont windowPkg
  have refined :=
    DyadicIntervalPacket_nested_refinement_ledger packet sameLeft sameRight sameProvenance
      widthRow' midpointRow' radiusRow' orderRow' endpointRow' endpointPkg
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed refined.left.right.right.right.right.right.right.right.left
      refined.left.right.right.left sealCont
  have windowUnary : UnaryHistory windowRow :=
    unary_cont_closed sealUnary refined.left.right.right.right.right.left windowCont
  exact
    And.intro refined.left
      (And.intro sealUnary
        (And.intro windowUnary
          (And.intro refined.right.left
            (And.intro refined.right.right.right.left windowPkg))))

theorem DyadicIntervalPacket_nested_window_name_certificate [AskSetup] [PackageSetup]
    {left0 right0 width0 midpoint0 radius0 order0 provenance0 endpoint0 left1 right1 width1
      midpoint1 radius1 order1 provenance1 endpoint1 left2 right2 width2 midpoint2 radius2
      order2 provenance2 endpoint2 sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left0 right0 width0 midpoint0 radius0 order0 provenance0 endpoint0
        bundle pkg ->
      hsame left0 left1 ->
        hsame right0 right1 ->
          hsame provenance0 provenance1 ->
            Cont left1 right1 width1 ->
              Cont left1 width1 midpoint1 ->
                Cont right1 width1 radius1 ->
                  Cont midpoint1 radius1 order1 ->
                    Cont order1 provenance1 endpoint1 ->
                      PkgSig bundle endpoint1 pkg ->
                        hsame left1 left2 ->
                          hsame right1 right2 ->
                            hsame provenance1 provenance2 ->
                              Cont left2 right2 width2 ->
                                Cont left2 width2 midpoint2 ->
                                  Cont right2 width2 radius2 ->
                                    Cont midpoint2 radius2 order2 ->
                                      Cont order2 provenance2 endpoint2 ->
                                        PkgSig bundle endpoint2 pkg ->
                                          Cont endpoint2 width2 sealRow ->
                                            PkgSig bundle sealRow pkg ->
                                              SemanticNameCert
                                                  (fun e : BHist =>
                                                    DyadicIntervalPacket left2 right2 width2
                                                      midpoint2 radius2 order2 provenance2 e
                                                      bundle pkg)
                                                  (fun e : BHist =>
                                                    DyadicIntervalPacket left2 right2 width2
                                                      midpoint2 radius2 order2 provenance2 e
                                                      bundle pkg)
                                                  (fun e : BHist =>
                                                    DyadicIntervalPacket left2 right2 width2
                                                      midpoint2 radius2 order2 provenance2 e
                                                      bundle pkg)
                                                  (fun a b : BHist =>
                                                    DyadicIntervalPacket left2 right2 width2
                                                        midpoint2 radius2 order2 provenance2 a
                                                        bundle pkg ∧
                                                      DyadicIntervalPacket left2 right2 width2
                                                        midpoint2 radius2 order2 provenance2 b
                                                        bundle pkg ∧
                                                        hsame a b) ∧
                                                hsame endpoint0 endpoint2 ∧
                                                  UnaryHistory sealRow ∧
                                                    hsame sealRow (append endpoint2 width2) ∧
                                                      PkgSig bundle sealRow pkg := by
  intro packet0 sameLeft01 sameRight01 sameProvenance01 widthRow1 midpointRow1 radiusRow1
    orderRow1 endpointRow1 pkgRow1 sameLeft12 sameRight12 sameProvenance12 widthRow2
    midpointRow2 radiusRow2 orderRow2 endpointRow2 pkgRow2 sealRowCont sealRowPkg
  have step1 :=
    DyadicIntervalPacket_nested_refinement_ledger packet0 sameLeft01 sameRight01
      sameProvenance01 widthRow1 midpointRow1 radiusRow1 orderRow1 endpointRow1 pkgRow1
  have packet1 :
      DyadicIntervalPacket left1 right1 width1 midpoint1 radius1 order1 provenance1 endpoint1
        bundle pkg :=
    step1.left
  have sameEndpoint01 : hsame endpoint0 endpoint1 :=
    step1.right.right.right.right.right
  have step2 :=
    DyadicIntervalPacket_nested_refinement_ledger packet1 sameLeft12 sameRight12
      sameProvenance12 widthRow2 midpointRow2 radiusRow2 orderRow2 endpointRow2 pkgRow2
  have packet2 :
      DyadicIntervalPacket left2 right2 width2 midpoint2 radius2 order2 provenance2 endpoint2
        bundle pkg :=
    step2.left
  have sameEndpoint12 : hsame endpoint1 endpoint2 :=
    step2.right.right.right.right.right
  have sameEndpoint02 : hsame endpoint0 endpoint2 :=
    hsame_trans sameEndpoint01 sameEndpoint12
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed packet2.right.right.right.right.right.right.right.left packet2.right.right.left
      sealRowCont
  have cert :
      SemanticNameCert
          (fun e : BHist =>
            DyadicIntervalPacket left2 right2 width2 midpoint2 radius2 order2 provenance2 e
              bundle pkg)
          (fun e : BHist =>
            DyadicIntervalPacket left2 right2 width2 midpoint2 radius2 order2 provenance2 e
              bundle pkg)
          (fun e : BHist =>
            DyadicIntervalPacket left2 right2 width2 midpoint2 radius2 order2 provenance2 e
              bundle pkg)
          (fun a b : BHist =>
            DyadicIntervalPacket left2 right2 width2 midpoint2 radius2 order2 provenance2 a
                bundle pkg ∧
              DyadicIntervalPacket left2 right2 width2 midpoint2 radius2 order2 provenance2 b
                bundle pkg ∧
                hsame a b) := {
    core := {
      carrier_inhabited := Exists.intro endpoint2 packet2
      equiv_refl := by
        intro row source
        exact And.intro source (And.intro source (hsame_refl row))
      equiv_symm := by
        intro row row' classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro row row' row'' classifiedLeft classifiedRight
        exact And.intro classifiedLeft.left
          (And.intro classifiedRight.right.left
            (hsame_trans classifiedLeft.right.right classifiedRight.right.right))
      carrier_respects_equiv := by
        intro row row' classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro sameEndpoint02
      (And.intro sealUnary
        (And.intro sealRowCont sealRowPkg)))

end BEDC.Derived.DyadicIntervalUp
