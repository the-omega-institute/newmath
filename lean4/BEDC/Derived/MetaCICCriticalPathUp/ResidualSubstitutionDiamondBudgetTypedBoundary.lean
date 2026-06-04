import BEDC.Derived.MetaCICCriticalPathUp.ResidualSubstitutionDiamondBudget

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualSubstitutionDiamondBudgetTypedBoundary
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName closedRead residualRead mediatedRead frontierRead checkerRead typedBoundary
      l10Read boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont transport route closedRead ->
        Cont handoff dischargeSocket residualRead ->
          Cont strongNorm normalForm mediatedRead ->
            Cont closedRead residualRead frontierRead ->
              Cont frontierRead transport checkerRead ->
                Cont checkerRead normalForm typedBoundary ->
                  Cont typedBoundary localName l10Read ->
                    Cont l10Read handoff boundedRead ->
                      PkgSig bundle typedBoundary pkg ->
                        PkgSig bundle boundedRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row boundedRead ∧
                                UnaryHistory row)
                              (fun row : BHist =>
                                hsame row closedRead ∨ hsame row residualRead ∨
                                  hsame row mediatedRead ∨ hsame row frontierRead ∨
                                    hsame row checkerRead ∨ hsame row typedBoundary ∨
                                      hsame row l10Read ∨ hsame row boundedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧
                                  Cont checkerRead normalForm typedBoundary ∧
                                    Cont typedBoundary localName l10Read ∧
                                      Cont l10Read handoff boundedRead ∧
                                        PkgSig bundle typedBoundary pkg ∧
                                          PkgSig bundle boundedRead pkg)
                              hsame ∧
                            UnaryHistory typedBoundary ∧ UnaryHistory l10Read ∧
                              UnaryHistory boundedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet transportRouteClosed handoffSocketResidual strongNormalMediated
    closedResidualFrontier frontierTransportChecker checkerNormalTyped typedLocalL10
    l10HandoffBounded typedBoundaryPkg boundedPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary, localNameUnary,
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
  have typedUnary : UnaryHistory typedBoundary :=
    unary_cont_closed checkerUnary normalFormUnary checkerNormalTyped
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed typedUnary localNameUnary typedLocalL10
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed l10Unary handoffUnary l10HandoffBounded
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row closedRead ∨ hsame row residualRead ∨ hsame row mediatedRead ∨
              hsame row frontierRead ∨ hsame row checkerRead ∨ hsame row typedBoundary ∨
                hsame row l10Read ∨ hsame row boundedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont checkerRead normalForm typedBoundary ∧
              Cont typedBoundary localName l10Read ∧ Cont l10Read handoff boundedRead ∧
                PkgSig bundle typedBoundary pkg ∧ PkgSig bundle boundedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundedRead ⟨hsame_refl boundedRead, boundedUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, checkerNormalTyped, typedLocalL10, l10HandoffBounded,
          typedBoundaryPkg, boundedPkg⟩
  }
  exact ⟨cert, typedUnary, l10Unary, boundedUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
