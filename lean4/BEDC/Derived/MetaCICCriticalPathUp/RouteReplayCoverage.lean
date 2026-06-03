import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRouteReplayCoverage [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName replayRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm replayRead →
        Cont obstruction dischargeSocket socketRead →
          PkgSig bundle replayRead pkg →
            PkgSig bundle socketRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                      hsame row handoff ∨ hsame row dischargeSocket ∨
                        hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                          hsame row localName ∨ hsame row replayRead ∨
                            hsame row socketRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont strongNorm normalForm replayRead ∧
                      Cont obstruction dischargeSocket socketRead ∧
                        PkgSig bundle replayRead pkg ∧ PkgSig bundle socketRead pkg)
                  hsame ∧
                UnaryHistory replayRead ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet strongNormNormalFormReplay obstructionSocketRead replayReadPkg socketReadPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormReplay
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed obstructionUnary dischargeSocketUnary obstructionSocketRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row replayRead ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont strongNorm normalForm replayRead ∧
              Cont obstruction dischargeSocket socketRead ∧ PkgSig bundle replayRead pkg ∧
                PkgSig bundle socketRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, strongNormNormalFormReplay, obstructionSocketRead, replayReadPkg,
          socketReadPkg⟩
  }
  exact ⟨cert, replayReadUnary, socketReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
