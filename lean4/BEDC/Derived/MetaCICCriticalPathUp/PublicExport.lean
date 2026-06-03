import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPublicExport [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet routeLocalNamePublic publicPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNamePublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      intro row source
      have samePublic : hsame row publicRead := source.left
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr samePublic))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

theorem MetaCICCriticalPathPublicInterface [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName l10Read candidateRead confluenceRead decidabilityRead residualRead
      interfaceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName l10Read →
        Cont l10Read handoff candidateRead →
          Cont candidateRead normalForm confluenceRead →
            Cont confluenceRead obstruction decidabilityRead →
              Cont decidabilityRead dischargeSocket residualRead →
                Cont residualRead provenance interfaceRead →
                  PkgSig bundle interfaceRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row interfaceRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row l10Read ∨ hsame row candidateRead ∨
                            hsame row confluenceRead ∨ hsame row decidabilityRead ∨
                              hsame row residualRead ∨ hsame row interfaceRead)
                        (fun row : BHist =>
                          hsame row interfaceRead ∧ PkgSig bundle interfaceRead pkg ∧
                            PkgSig bundle provenance pkg)
                        hsame ∧
                      UnaryHistory interfaceRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameL10 l10HandoffCandidate candidateNormalConfluence
    confluenceObstructionDecidability decidabilitySocketResidual residualProvenanceInterface
    interfacePkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameL10
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed l10Unary handoffUnary l10HandoffCandidate
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed candidateUnary normalFormUnary candidateNormalConfluence
  have decidabilityUnary : UnaryHistory decidabilityRead :=
    unary_cont_closed confluenceUnary obstructionUnary confluenceObstructionDecidability
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed decidabilityUnary dischargeSocketUnary decidabilitySocketResidual
  have interfaceUnary : UnaryHistory interfaceRead :=
    unary_cont_closed residualUnary provenanceUnary residualProvenanceInterface
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row interfaceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row l10Read ∨ hsame row candidateRead ∨ hsame row confluenceRead ∨
              hsame row decidabilityRead ∨ hsame row residualRead ∨ hsame row interfaceRead)
          (fun row : BHist =>
            hsame row interfaceRead ∧ PkgSig bundle interfaceRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro interfaceRead
        ⟨hsame_refl interfaceRead, interfaceUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, interfacePkg, provenancePkg⟩
  }
  exact ⟨cert, interfaceUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
