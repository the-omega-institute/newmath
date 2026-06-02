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

theorem MetaCICCriticalPathSubstitutionHandoffVisibility [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName substitutionRead replayed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      hsame substitutionRead handoff →
        Cont substitutionRead route replayed →
          PkgSig bundle replayed pkg →
            SemanticNameCert
                (fun row : BHist => hsame row replayed ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row handoff ∨ hsame row route ∨ hsame row replayed ∨
                    hsame row obstruction ∨ hsame row dischargeSocket)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle replayed pkg)
                hsame ∧
              UnaryHistory substitutionRead ∧ UnaryHistory replayed ∧
                hsame transport localName := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro packet substitutionHandoff substitutionRouteReplay replayedPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  have substitutionUnary : UnaryHistory substitutionRead :=
    unary_transport handoffUnary (hsame_symm substitutionHandoff)
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed substitutionUnary routeUnary substitutionRouteReplay
  have sourceReplayed :
      (fun row : BHist => hsame row replayed ∧ UnaryHistory row) replayed := by
    exact ⟨hsame_refl replayed, replayedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayed ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row route ∨ hsame row replayed ∨
              hsame row obstruction ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle replayed pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayed sourceReplayed
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, replayedPkg⟩
  }
  exact ⟨cert, substitutionUnary, replayedUnary, transportLocalName⟩

end BEDC.Derived.MetaCICCriticalPathUp
