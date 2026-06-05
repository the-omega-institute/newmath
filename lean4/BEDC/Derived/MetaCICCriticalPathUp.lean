import BEDC.Derived.MetaCICCriticalPathUp.Core
import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPublicRouteCertificate [AskSetup] [PackageSetup]
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
                  hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                    hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro packet routeLocalNamePublic publicPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _socketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNamePublic
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg, provenancePkg⟩
  }
  exact ⟨cert, publicUnary⟩

theorem MetaCICCriticalPathPhaseRealRouteBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName streamSchedule regSeqReadback realSeal phaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName streamSchedule →
        Cont streamSchedule localName regSeqReadback →
          Cont regSeqReadback localName realSeal →
            Cont realSeal provenance phaseRead →
              PkgSig bundle phaseRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row route ∨ hsame row streamSchedule ∨
                        hsame row regSeqReadback ∨ hsame row realSeal ∨
                          hsame row phaseRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont route localName streamSchedule ∧
                        Cont streamSchedule localName regSeqReadback ∧
                          Cont regSeqReadback localName realSeal ∧
                            Cont realSeal provenance phaseRead ∧
                              PkgSig bundle phaseRead pkg)
                    hsame ∧
                  UnaryHistory phaseRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro packet routeLocalNameSchedule scheduleLocalNameReadback readbackLocalNameSeal
    sealProvenancePhase phasePkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _socketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have scheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSchedule
  have readbackUnary : UnaryHistory regSeqReadback :=
    unary_cont_closed scheduleUnary localNameUnary scheduleLocalNameReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary localNameUnary readbackLocalNameSeal
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed realSealUnary provenanceUnary sealProvenancePhase
  have sourcePhase :
      (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row) phaseRead := by
    exact ⟨hsame_refl phaseRead, phaseUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row route ∨ hsame row streamSchedule ∨ hsame row regSeqReadback ∨
              hsame row realSeal ∨ hsame row phaseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route localName streamSchedule ∧
              Cont streamSchedule localName regSeqReadback ∧
                Cont regSeqReadback localName realSeal ∧
                  Cont realSeal provenance phaseRead ∧ PkgSig bundle phaseRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro phaseRead sourcePhase
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
      exact
        ⟨source.right, routeLocalNameSchedule, scheduleLocalNameReadback,
          readbackLocalNameSeal, sealProvenancePhase, phasePkg⟩
  }
  exact ⟨cert, phaseUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
