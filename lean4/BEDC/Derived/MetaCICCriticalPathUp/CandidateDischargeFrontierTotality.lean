import BEDC.Derived.MetaCICCriticalPathUp.Core

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateDischargeFrontierTotality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName boundedConversion confluenceRead readinessRead socketRead totalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm boundedConversion →
        Cont boundedConversion handoff confluenceRead →
          Cont confluenceRead route readinessRead →
            Cont readinessRead dischargeSocket socketRead →
              Cont socketRead obstruction totalRead →
                PkgSig bundle totalRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row strongNorm ∨ hsame row normalForm ∨
                          hsame row obstruction ∨ hsame row handoff ∨
                            hsame row dischargeSocket ∨ hsame row readinessRead ∨
                              hsame row socketRead ∨ hsame row totalRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont readinessRead dischargeSocket socketRead ∧
                          Cont socketRead obstruction totalRead ∧
                            PkgSig bundle totalRead pkg ∧ PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory boundedConversion ∧ UnaryHistory confluenceRead ∧
                      UnaryHistory readinessRead ∧ UnaryHistory socketRead ∧
                        UnaryHistory totalRead := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg hsame SemanticNameCert
  intro packet boundedRoute confluenceRoute readinessRoute socketRoute totalRoute totalPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have boundedUnary : UnaryHistory boundedConversion :=
    unary_cont_closed strongNormUnary normalFormUnary boundedRoute
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed boundedUnary handoffUnary confluenceRoute
  have readinessUnary : UnaryHistory readinessRead :=
    unary_cont_closed confluenceUnary routeUnary readinessRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed readinessUnary dischargeSocketUnary socketRoute
  have totalUnary : UnaryHistory totalRead :=
    unary_cont_closed socketUnary obstructionUnary totalRoute
  have sourceTotal :
      (fun row : BHist => hsame row totalRead ∧ UnaryHistory row) totalRead := by
    exact ⟨hsame_refl totalRead, totalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row readinessRead ∨
                hsame row socketRead ∨ hsame row totalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont readinessRead dischargeSocket socketRead ∧
              Cont socketRead obstruction totalRead ∧ PkgSig bundle totalRead pkg ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro totalRead sourceTotal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketRoute, totalRoute, totalPkg, provenancePkg⟩
  }
  exact ⟨cert, boundedUnary, confluenceUnary, readinessUnary, socketUnary, totalUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
