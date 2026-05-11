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

def DyadicIntervalEndpointPacket [AskSetup] [PackageSetup]
    (left right width order midpoint radius hsameLedger contLedger pkgrow nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hsameLedger ∧ UnaryHistory width ∧ Cont left right order ∧
    Cont left right midpoint ∧ Cont midpoint width radius ∧ Cont order radius contLedger ∧
      Cont contLedger pkgrow nameRow ∧ PkgSig bundle pkgrow pkg

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

end BEDC.Derived.DyadicIntervalUp
