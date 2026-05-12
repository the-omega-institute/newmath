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

theorem LagrangianMechanicsPacket_eulerlagrange_interface [AskSetup] [PackageSetup]
    {configuration velocity action variation endpoint residual symplectic current transport route
      provenance certificate residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LagrangianMechanicsPacket configuration velocity action variation endpoint residual symplectic
        current transport route provenance certificate bundle pkg ->
      Cont action variation endpoint ->
        Cont endpoint residual residualRead ->
          PkgSig bundle residualRead pkg ->
            UnaryHistory residual ∧ UnaryHistory residualRead ∧ Cont action variation endpoint ∧
              Cont endpoint residual residualRead ∧ PkgSig bundle certificate pkg ∧
                PkgSig bundle residualRead pkg := by
  intro packet actionVariationEndpoint endpointResidualRead residualReadPkg
  obtain ⟨_configurationUnary, _velocityUnary, variationUnary, residualUnary,
    _symplecticUnary, _transportUnary, _provenanceUnary, _configurationVelocityAction,
    _packetActionVariationEndpoint, _residualSymplecticCurrent, _currentTransportRoute,
    _routeProvenanceCertificate, certificatePkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed
      (unary_cont_closed _configurationUnary _velocityUnary _configurationVelocityAction)
      variationUnary actionVariationEndpoint
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed endpointUnary residualUnary endpointResidualRead
  exact
    ⟨residualUnary, residualReadUnary, actionVariationEndpoint, endpointResidualRead,
      certificatePkg, residualReadPkg⟩

end BEDC.Derived.LagrangianMechanicsUp
