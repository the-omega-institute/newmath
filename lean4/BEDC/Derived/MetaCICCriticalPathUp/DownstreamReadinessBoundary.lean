import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_downstream_readiness_boundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg ->
      Cont route localName downstream ->
        PkgSig bundle downstream pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
              (fun row : BHist =>
                Cont strongNorm normalForm route ∧ Cont handoff obstruction dischargeSocket ∧
                  (hsame row route ∨ hsame row localName ∨ hsame row downstream))
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle downstream pkg)
              hsame ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameDownstream downstreamPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    localNameUnary, strongNormNormalFormRoute, handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameDownstream
  have sourceDownstream :
      (fun row : BHist => hsame row downstream ∧ UnaryHistory row) downstream := by
    exact ⟨hsame_refl downstream, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont strongNorm normalForm route ∧ Cont handoff obstruction dischargeSocket ∧
              (hsame row route ∨ hsame row localName ∨ hsame row downstream))
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle downstream pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstream sourceDownstream
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨strongNormNormalFormRoute, handoffObstructionSocket,
          Or.inr (Or.inr source.left)⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, downstreamPkg⟩
  }
  exact ⟨cert, provenancePkg⟩

theorem MetaCICCriticalPathRootConsumerReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName readiness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg ->
      Cont route localName readiness ->
        PkgSig bundle readiness pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row readiness ∧ UnaryHistory row)
              (fun row : BHist =>
                Cont strongNorm normalForm route ∧ Cont handoff obstruction dischargeSocket ∧
                  (hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                    hsame row dischargeSocket ∨ hsame row route ∨ hsame row localName ∨
                      hsame row readiness))
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle readiness pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory obstruction ∧ UnaryHistory dischargeSocket ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameReadiness readinessPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    localNameUnary, strongNormNormalFormRoute, handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have readinessUnary : UnaryHistory readiness :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameReadiness
  have sourceReadiness :
      (fun row : BHist => hsame row readiness ∧ UnaryHistory row) readiness := by
    exact ⟨hsame_refl readiness, readinessUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readiness ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont strongNorm normalForm route ∧ Cont handoff obstruction dischargeSocket ∧
              (hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                hsame row dischargeSocket ∨ hsame row route ∨ hsame row localName ∨
                  hsame row readiness))
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle readiness pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readiness sourceReadiness
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨strongNormNormalFormRoute, handoffObstructionSocket,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, readinessPkg, provenancePkg⟩
  }
  exact ⟨cert, obstructionUnary, dischargeSocketUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
