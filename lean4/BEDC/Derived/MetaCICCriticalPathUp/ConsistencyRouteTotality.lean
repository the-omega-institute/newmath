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

theorem MetaCICCriticalPathPacket_consistency_route_totality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName consistencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm consistencyRead →
        PkgSig bundle consistencyRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row consistencyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                    hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                      hsame row consistencyRead)
              (fun row : BHist =>
                PkgSig bundle row pkg ∧ Cont strongNorm normalForm consistencyRead ∧
                  hsame transport localName)
              hsame ∧
            UnaryHistory consistencyRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet strongNormNormalFormConsistency consistencyPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  have consistencyUnary : UnaryHistory consistencyRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormConsistency
  have sourceConsistency :
      (fun row : BHist => hsame row consistencyRead ∧ UnaryHistory row) consistencyRead := by
    exact ⟨hsame_refl consistencyRead, consistencyUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consistencyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row consistencyRead)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ Cont strongNorm normalForm consistencyRead ∧
              hsame transport localName)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consistencyRead sourceConsistency
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨consistencyPkg, strongNormNormalFormConsistency, transportLocalName⟩
  }
  exact ⟨cert, consistencyUnary, provenancePkg⟩

theorem MetaCICCriticalPathConsistencyRouteTotality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName consistencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route transport consistencyRead →
        PkgSig bundle consistencyRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row consistencyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                    hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                      hsame row consistencyRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consistencyRead pkg)
              hsame ∧
            UnaryHistory consistencyRead ∧ Cont strongNorm normalForm route ∧
              hsame transport localName ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeTransportConsistency consistencyPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary,
    _localNameUnary, strongNormNormalFormRoute, _handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  have consistencyUnary : UnaryHistory consistencyRead :=
    unary_cont_closed routeUnary transportUnary routeTransportConsistency
  have consistencySource :
      (fun row : BHist => hsame row consistencyRead ∧ UnaryHistory row)
          consistencyRead := by
    exact ⟨hsame_refl consistencyRead, consistencyUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consistencyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row consistencyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle consistencyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consistencyRead consistencySource
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, consistencyPkg⟩
  }
  exact
    ⟨cert, consistencyUnary, strongNormNormalFormRoute, transportLocalName, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
