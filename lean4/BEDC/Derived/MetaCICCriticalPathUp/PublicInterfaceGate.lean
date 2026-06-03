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

theorem MetaCICCriticalPathPublicInterfaceGate [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance localName
      l10Read candidateFrontier residualSocket confluenceBudget gateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont route provenance l10Read →
        Cont l10Read handoff candidateFrontier →
          Cont candidateFrontier dischargeSocket residualSocket →
            Cont residualSocket obstruction confluenceBudget →
              Cont confluenceBudget localName gateRead →
                PkgSig bundle gateRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row gateRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row l10Read ∨ hsame row candidateFrontier ∨
                          hsame row residualSocket ∨ hsame row confluenceBudget ∨
                            hsame row gateRead)
                      (fun row : BHist =>
                        hsame row gateRead ∧ PkgSig bundle gateRead pkg ∧
                          PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory gateRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeProvenance l10Handoff candidateDischarge residualObstruction
    confluenceLocalName gatePkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed routeUnary provenanceUnary routeProvenance
  have candidateUnary : UnaryHistory candidateFrontier :=
    unary_cont_closed l10Unary handoffUnary l10Handoff
  have residualUnary : UnaryHistory residualSocket :=
    unary_cont_closed candidateUnary dischargeSocketUnary candidateDischarge
  have confluenceUnary : UnaryHistory confluenceBudget :=
    unary_cont_closed residualUnary obstructionUnary residualObstruction
  have gateUnary : UnaryHistory gateRead :=
    unary_cont_closed confluenceUnary localNameUnary confluenceLocalName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gateRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row l10Read ∨ hsame row candidateFrontier ∨ hsame row residualSocket ∨
              hsame row confluenceBudget ∨ hsame row gateRead)
          (fun row : BHist =>
            hsame row gateRead ∧ PkgSig bundle gateRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gateRead ⟨hsame_refl gateRead, gateUnary⟩
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
      exact ⟨source.left, gatePkg, provenancePkg⟩
  }
  exact ⟨cert, gateUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
