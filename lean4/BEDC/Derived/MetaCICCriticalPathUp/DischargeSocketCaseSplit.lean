import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathDischargeSocketCaseSplit [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName filledRead residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont handoff obstruction filledRead →
        Cont dischargeSocket localName residualRead →
          PkgSig bundle filledRead pkg →
            PkgSig bundle residualRead pkg →
              SemanticNameCert
                    (fun row : BHist =>
                      (hsame row filledRead ∨ hsame row obstruction ∨
                          hsame row residualRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row dischargeSocket ∨ hsame row obstruction ∨
                        hsame row filledRead ∨ hsame row residualRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle filledRead pkg ∧
                        PkgSig bundle residualRead pkg)
                    hsame ∧
                UnaryHistory filledRead ∧ UnaryHistory residualRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet handoffObstructionFilled socketLocalNameResidual filledPkg residualPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have filledUnary : UnaryHistory filledRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionFilled
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed dischargeSocketUnary localNameUnary socketLocalNameResidual
  have sourceFilled :
      (fun row : BHist =>
        (hsame row filledRead ∨ hsame row obstruction ∨ hsame row residualRead) ∧
          UnaryHistory row) filledRead := by
    exact ⟨Or.inl (hsame_refl filledRead), filledUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row filledRead ∨ hsame row obstruction ∨ hsame row residualRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row dischargeSocket ∨ hsame row obstruction ∨ hsame row filledRead ∨
              hsame row residualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle filledRead pkg ∧
              PkgSig bundle residualRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro filledRead sourceFilled
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
        constructor
        · cases source.left with
          | inl sameFilled =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameFilled)
          | inr rest =>
              cases rest with
              | inl sameObstruction =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameObstruction))
              | inr sameResidual =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameResidual))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFilled =>
          exact Or.inr (Or.inr (Or.inl sameFilled))
      | inr rest =>
          cases rest with
          | inl sameObstruction =>
              exact Or.inr (Or.inl sameObstruction)
          | inr sameResidual =>
              exact Or.inr (Or.inr (Or.inr sameResidual))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, filledPkg, residualPkg⟩
  }
  exact ⟨cert, filledUnary, residualUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
