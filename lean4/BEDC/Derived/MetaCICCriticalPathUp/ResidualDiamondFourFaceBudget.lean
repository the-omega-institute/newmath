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

theorem MetaCICCriticalPathResidualDiamondFourFaceBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName residualRead normalizationRead frontierRead diamondRead boundedRead l10Read
      sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont handoff route residualRead →
        Cont strongNorm normalForm normalizationRead →
          Cont residualRead normalizationRead frontierRead →
            Cont frontierRead transport diamondRead →
              Cont diamondRead dischargeSocket boundedRead →
                Cont boundedRead handoff l10Read →
                  Cont l10Read provenance sourceRead →
                    PkgSig bundle frontierRead pkg →
                      PkgSig bundle sourceRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row residualRead ∨ hsame row normalizationRead ∨
                                hsame row frontierRead ∨ hsame row diamondRead ∨
                                  hsame row boundedRead ∨ hsame row l10Read ∨
                                    hsame row sourceRead ∨ hsame row dischargeSocket)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                                PkgSig bundle sourceRead pkg)
                            hsame ∧
                          UnaryHistory residualRead ∧ UnaryHistory normalizationRead ∧
                            UnaryHistory frontierRead ∧ UnaryHistory diamondRead ∧
                              UnaryHistory boundedRead ∧ UnaryHistory l10Read ∧
                                UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet handoffRouteResidual strongNormalNormalization residualNormalizationFrontier
    frontierTransportDiamond diamondSocketBounded boundedHandoffL10 l10ProvenanceSource
    frontierPkg sourcePkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary routeUnary handoffRouteResidual
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormalNormalization
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed residualUnary normalizationUnary residualNormalizationFrontier
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed frontierUnary transportUnary frontierTransportDiamond
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed diamondUnary dischargeSocketUnary diamondSocketBounded
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed boundedUnary handoffUnary boundedHandoffL10
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed l10Unary provenanceUnary l10ProvenanceSource
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualRead ∨ hsame row normalizationRead ∨
              hsame row frontierRead ∨ hsame row diamondRead ∨
                hsame row boundedRead ∨ hsame row l10Read ∨
                  hsame row sourceRead ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
              PkgSig bundle sourceRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceUnary⟩
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
                  (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, sourcePkg⟩
  }
  exact
    ⟨cert, residualUnary, normalizationUnary, frontierUnary, diamondUnary, boundedUnary,
      l10Unary, sourceUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
