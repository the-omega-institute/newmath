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

theorem LagrangianMechanicsPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {configuration velocity action variation endpoint residual symplectic current transport route
      provenance certificate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LagrangianMechanicsPacket configuration velocity action variation endpoint residual symplectic
        current transport route provenance certificate bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row certificate ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist =>
          UnaryHistory configuration ∧ UnaryHistory velocity ∧ UnaryHistory action ∧
            UnaryHistory variation ∧ UnaryHistory endpoint ∧ UnaryHistory residual ∧
              UnaryHistory symplectic ∧ UnaryHistory current ∧ UnaryHistory transport ∧
                UnaryHistory route ∧ UnaryHistory provenance ∧
                  Cont configuration velocity action ∧ Cont action variation endpoint ∧
                    Cont residual symplectic current ∧ Cont current transport route ∧
                      Cont route provenance row)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont route provenance row)
        (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') := by
  intro packet
  obtain ⟨configurationUnary, velocityUnary, variationUnary, residualUnary, symplecticUnary,
    transportUnary, provenanceUnary, configurationVelocityAction, actionVariationEndpoint,
    residualSymplecticCurrent, currentTransportRoute, routeProvenanceCertificate,
    certificatePkg⟩ := packet
  have actionUnary : UnaryHistory action :=
    unary_cont_closed configurationUnary velocityUnary configurationVelocityAction
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed actionUnary variationUnary actionVariationEndpoint
  have currentUnary : UnaryHistory current :=
    unary_cont_closed residualUnary symplecticUnary residualSymplecticCurrent
  have routeUnary : UnaryHistory route :=
    unary_cont_closed currentUnary transportUnary currentTransportRoute
  have certificateUnary : UnaryHistory certificate :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCertificate
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro certificate
          ⟨hsame_refl certificate, certificateUnary, certificatePkg⟩
      equiv_refl := by
        intro row sourceRow
        exact
          ⟨PkgSig_psame_intro sourceRow.right.right sourceRow.right.right
            (hsame_refl row), hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact
        ⟨configurationUnary, velocityUnary, actionUnary, variationUnary, endpointUnary,
          residualUnary, symplecticUnary, currentUnary, transportUnary, routeUnary,
          provenanceUnary, configurationVelocityAction, actionVariationEndpoint,
          residualSymplecticCurrent, currentTransportRoute, routeProvenanceCertificate⟩
    ledger_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact ⟨certificatePkg, routeProvenanceCertificate⟩
  }

end BEDC.Derived.LagrangianMechanicsUp
