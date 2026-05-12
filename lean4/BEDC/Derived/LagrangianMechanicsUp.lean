import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LagrangianMechanicsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem LagrangianMechanicsPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {configuration velocity action variation endpoint residual symplectic current transport route
      provenance certificate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LagrangianMechanicsPacket configuration velocity action variation endpoint residual symplectic
        current transport route provenance certificate bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row certificate ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => Cont route provenance row ∧ UnaryHistory current ∧
          UnaryHistory symplectic)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont residual symplectic current ∧
          Cont current transport route)
        (fun row row' : BHist => hsame row row') := by
  intro packet
  obtain ⟨_configurationUnary, _velocityUnary, _variationUnary, residualUnary,
    symplecticUnary, transportUnary, provenanceUnary, _configurationVelocityAction,
    _actionVariationEndpoint, residualSymplecticCurrent, currentTransportRoute,
    routeProvenanceCertificate, certificatePkg⟩ := packet
  have currentUnary : UnaryHistory current :=
    unary_cont_closed residualUnary symplecticUnary residualSymplecticCurrent
  have routeUnary : UnaryHistory route :=
    unary_cont_closed currentUnary transportUnary currentTransportRoute
  have certificateUnary : UnaryHistory certificate :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCertificate
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro certificate ⟨hsame_refl certificate, certificateUnary, certificatePkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      exact
        ⟨cont_result_hsame_transport routeProvenanceCertificate (hsame_symm sourceRow.left),
          currentUnary, symplecticUnary⟩
    ledger_sound := by
      intro row sourceRow
      exact ⟨sourceRow.right.right, residualSymplecticCurrent, currentTransportRoute⟩
  }

end BEDC.Derived.LagrangianMechanicsUp
