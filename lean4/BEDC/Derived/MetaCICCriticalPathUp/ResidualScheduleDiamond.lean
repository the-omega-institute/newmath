import BEDC.Derived.MetaCICCriticalPathUp.Core
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualScheduleDiamond [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName residualSchedule localDiamond : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName residualSchedule ->
        Cont residualSchedule obstruction localDiamond ->
          PkgSig bundle localDiamond pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row localDiamond ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row route ∨ hsame row residualSchedule ∨
                    hsame row obstruction ∨ hsame row localDiamond)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont route localName residualSchedule ∧
                    Cont residualSchedule obstruction localDiamond ∧
                      PkgSig bundle localDiamond pkg)
                hsame ∧ UnaryHistory localDiamond := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameSchedule scheduleObstructionDiamond diamondPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, _provenancePkg⟩ := packet
  have residualScheduleUnary : UnaryHistory residualSchedule :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSchedule
  have localDiamondUnary : UnaryHistory localDiamond :=
    unary_cont_closed residualScheduleUnary obstructionUnary scheduleObstructionDiamond
  have sourceDiamond :
      (fun row : BHist => hsame row localDiamond ∧ UnaryHistory row) localDiamond := by
    exact ⟨hsame_refl localDiamond, localDiamondUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localDiamond ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row route ∨ hsame row residualSchedule ∨ hsame row obstruction ∨
              hsame row localDiamond)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route localName residualSchedule ∧
              Cont residualSchedule obstruction localDiamond ∧ PkgSig bundle localDiamond pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localDiamond sourceDiamond
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeLocalNameSchedule, scheduleObstructionDiamond, diamondPkg⟩
  }
  exact ⟨cert, localDiamondUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
