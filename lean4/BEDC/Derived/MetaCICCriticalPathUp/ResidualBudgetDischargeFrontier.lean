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

theorem MetaCICCriticalPathResidualBudgetDischargeFrontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName residualRead substitutionRead premiseRead diamondRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont obstruction dischargeSocket residualRead →
        Cont residualRead transport substitutionRead →
          Cont substitutionRead handoff premiseRead →
            Cont premiseRead route diamondRead →
              Cont diamondRead localName frontierRead →
                PkgSig bundle frontierRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row residualRead ∨ hsame row substitutionRead ∨
                          hsame row premiseRead ∨ hsame row diamondRead ∨
                            hsame row frontierRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                          PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory frontierRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet obstructionSocketResidual residualTransportSubstitution
    substitutionHandoffPremise premiseRouteDiamond diamondLocalFrontier frontierPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed obstructionUnary dischargeSocketUnary obstructionSocketResidual
  have substitutionUnary : UnaryHistory substitutionRead :=
    unary_cont_closed residualUnary transportUnary residualTransportSubstitution
  have premiseUnary : UnaryHistory premiseRead :=
    unary_cont_closed substitutionUnary handoffUnary substitutionHandoffPremise
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed premiseUnary routeUnary premiseRouteDiamond
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed diamondUnary localNameUnary diamondLocalFrontier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualRead ∨ hsame row substitutionRead ∨ hsame row premiseRead ∨
              hsame row diamondRead ∨ hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, provenancePkg⟩
  }
  exact ⟨cert, frontierUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
