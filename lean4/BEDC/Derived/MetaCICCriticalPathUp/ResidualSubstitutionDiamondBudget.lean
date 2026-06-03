import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualSubstitutionDiamondBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName closedRead residualRead mediatedRead frontierRead checkerRead
      decidabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont transport route closedRead ->
        Cont handoff dischargeSocket residualRead ->
          Cont strongNorm normalForm mediatedRead ->
            Cont closedRead residualRead frontierRead ->
              Cont frontierRead transport checkerRead ->
                Cont checkerRead handoff decidabilityRead ->
                  PkgSig bundle frontierRead pkg ->
                    PkgSig bundle checkerRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row decidabilityRead ∧
                            UnaryHistory row)
                          (fun row : BHist =>
                            hsame row closedRead ∨ hsame row residualRead ∨
                              hsame row mediatedRead ∨ hsame row frontierRead ∨
                                hsame row checkerRead ∨ hsame row decidabilityRead ∨
                                  hsame row provenance)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                              PkgSig bundle checkerRead pkg)
                          hsame ∧
                        UnaryHistory closedRead ∧ UnaryHistory residualRead ∧
                          UnaryHistory mediatedRead ∧ UnaryHistory frontierRead ∧
                            UnaryHistory checkerRead ∧ UnaryHistory decidabilityRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet transportRouteClosed handoffSocketResidual strongNormalMediated
    closedResidualFrontier frontierTransportChecker checkerHandoffDecidability frontierPkg
    checkerPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed transportUnary routeUnary transportRouteClosed
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary dischargeSocketUnary handoffSocketResidual
  have mediatedUnary : UnaryHistory mediatedRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormalMediated
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed closedUnary residualUnary closedResidualFrontier
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed frontierUnary transportUnary frontierTransportChecker
  have decidabilityUnary : UnaryHistory decidabilityRead :=
    unary_cont_closed checkerUnary handoffUnary checkerHandoffDecidability
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row decidabilityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row closedRead ∨ hsame row residualRead ∨ hsame row mediatedRead ∨
              hsame row frontierRead ∨ hsame row checkerRead ∨
                hsame row decidabilityRead ∨ hsame row provenance)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
              PkgSig bundle checkerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro decidabilityRead ⟨hsame_refl decidabilityRead, decidabilityUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, checkerPkg⟩
  }
  exact
    ⟨cert, closedUnary, residualUnary, mediatedUnary, frontierUnary, checkerUnary,
      decidabilityUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
