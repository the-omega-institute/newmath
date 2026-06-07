import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathDownstreamConsumerReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName consumerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName consumerRead →
        Cont consumerRead handoff publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                    hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                      hsame row consumerRead ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont route localName consumerRead ∧
                    Cont consumerRead handoff publicRead ∧ PkgSig bundle publicRead pkg ∧
                      PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory consumerRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro packet routeLocalConsumer consumerHandoffPublic publicPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    _socketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalConsumer
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed consumerUnary handoffUnary consumerHandoffPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                hsame row consumerRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route localName consumerRead ∧
              Cont consumerRead handoff publicRead ∧ PkgSig bundle publicRead pkg ∧
                PkgSig bundle provenance pkg)
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
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeLocalConsumer, consumerHandoffPublic, publicPkg, provenancePkg⟩
  }
  exact ⟨cert, consumerUnary, publicUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
