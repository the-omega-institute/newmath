import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LagrangianMechanicsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LagrangianMechanicsPacket [AskSetup] [PackageSetup]
    (configuration velocity action variation endpoint residual symplectic current transport route
      provenance certificate : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory configuration ∧ UnaryHistory velocity ∧ UnaryHistory variation ∧
    UnaryHistory residual ∧ UnaryHistory symplectic ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ Cont configuration velocity action ∧
        Cont action variation endpoint ∧ Cont residual symplectic current ∧
          Cont current transport route ∧ Cont route provenance certificate ∧
            PkgSig bundle certificate pkg

theorem LagrangianMechanicsPacket_action_ledger_obligation [AskSetup] [PackageSetup]
    {configuration velocity action variation endpoint residual symplectic current transport route
      provenance certificate actionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LagrangianMechanicsPacket configuration velocity action variation endpoint residual symplectic
        current transport route provenance certificate bundle pkg ->
      Cont action variation actionRead ->
        UnaryHistory configuration ∧ UnaryHistory velocity ∧ UnaryHistory action ∧
          UnaryHistory variation ∧ UnaryHistory endpoint ∧ UnaryHistory actionRead ∧
            Cont configuration velocity action ∧ Cont action variation actionRead ∧
              hsame endpoint actionRead ∧ PkgSig bundle certificate pkg := by
  intro packet actionReadRow
  have configurationUnary : UnaryHistory configuration :=
    packet.left
  have velocityUnary : UnaryHistory velocity :=
    packet.right.left
  have variationUnary : UnaryHistory variation :=
    packet.right.right.left
  have actionRow : Cont configuration velocity action :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont action variation endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have actionUnary : UnaryHistory action :=
    unary_cont_closed configurationUnary velocityUnary actionRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed actionUnary variationUnary endpointRow
  have actionReadUnary : UnaryHistory actionRead :=
    unary_cont_closed actionUnary variationUnary actionReadRow
  have sameEndpoint : hsame endpoint actionRead :=
    cont_respects_hsame (hsame_refl action) (hsame_refl variation) endpointRow actionReadRow
  have pkgSig : PkgSig bundle certificate pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨configurationUnary, velocityUnary, actionUnary, variationUnary, endpointUnary,
      actionReadUnary, actionRow, actionReadRow, sameEndpoint, pkgSig⟩

theorem LagrangianMechanicsPacket_noether_consumer_boundary [AskSetup] [PackageSetup]
    {configuration velocity action variation endpoint residual symplectic current transport route
      provenance certificate noetherRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LagrangianMechanicsPacket configuration velocity action variation endpoint residual symplectic
        current transport route provenance certificate bundle pkg ->
      Cont symplectic current noetherRead ->
        PkgSig bundle noetherRead pkg ->
          UnaryHistory configuration ∧ UnaryHistory velocity ∧ UnaryHistory action ∧
            UnaryHistory variation ∧ UnaryHistory endpoint ∧ UnaryHistory residual ∧
              UnaryHistory symplectic ∧ UnaryHistory current ∧ UnaryHistory transport ∧
                UnaryHistory route ∧ UnaryHistory noetherRead ∧
                  Cont configuration velocity action ∧ Cont action variation endpoint ∧
                    Cont residual symplectic current ∧ Cont current transport route ∧
                      Cont symplectic current noetherRead ∧ PkgSig bundle certificate pkg ∧
                        PkgSig bundle noetherRead pkg := by
  intro packet noetherReadRow noetherPkg
  obtain ⟨configurationUnary, velocityUnary, variationUnary, residualUnary, symplecticUnary,
    transportUnary, _provenanceUnary, actionRow, endpointRow, currentRow, routeRow,
    _certificateRow, certificatePkg⟩ := packet
  have actionUnary : UnaryHistory action :=
    unary_cont_closed configurationUnary velocityUnary actionRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed actionUnary variationUnary endpointRow
  have currentUnary : UnaryHistory current :=
    unary_cont_closed residualUnary symplecticUnary currentRow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed currentUnary transportUnary routeRow
  have noetherUnary : UnaryHistory noetherRead :=
    unary_cont_closed symplecticUnary currentUnary noetherReadRow
  exact
    ⟨configurationUnary, velocityUnary, actionUnary, variationUnary, endpointUnary,
      residualUnary, symplecticUnary, currentUnary, transportUnary, routeUnary,
      noetherUnary, actionRow, endpointRow, currentRow, routeRow, noetherReadRow,
      certificatePkg, noetherPkg⟩

end BEDC.Derived.LagrangianMechanicsUp
