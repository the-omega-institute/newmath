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

theorem MetaCICCriticalPathDownstreamUnblockReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName rootRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName rootRead →
        Cont rootRead dischargeSocket consumerRead →
          PkgSig bundle consumerRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row rootRead ∨ hsame row consumerRead ∨
                    hsame row dischargeSocket) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                    hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                      hsame row localName ∨ hsame row rootRead ∨ hsame row consumerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle consumerRead pkg ∧
                    PkgSig bundle provenance pkg ∧ Cont rootRead dischargeSocket consumerRead)
                hsame ∧
              UnaryHistory rootRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalRoot rootSocketConsumer consumerPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalRoot
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed rootReadUnary dischargeSocketUnary rootSocketConsumer
  have sourceRoot :
      (fun row : BHist =>
        (hsame row rootRead ∨ hsame row consumerRead ∨ hsame row dischargeSocket) ∧
          UnaryHistory row) rootRead := by
    exact ⟨Or.inl (hsame_refl rootRead), rootReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row rootRead ∨ hsame row consumerRead ∨ hsame row dischargeSocket) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                hsame row localName ∨ hsame row rootRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle consumerRead pkg ∧
              PkgSig bundle provenance pkg ∧ Cont rootRead dischargeSocket consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceRoot
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
          | inl sameRoot =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameRoot)
          | inr rest =>
              cases rest with
              | inl sameConsumer =>
                  exact Or.inr (Or.inl
                    (hsame_trans (hsame_symm sameRows) sameConsumer))
              | inr sameSocket =>
                  exact Or.inr (Or.inr
                    (hsame_trans (hsame_symm sameRows) sameSocket))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameRoot =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl sameRoot)))))))
      | inr rest =>
          cases rest with
          | inl sameConsumer =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr sameConsumer)))))))
          | inr sameSocket =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSocket))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, consumerPkg, provenancePkg, rootSocketConsumer⟩
  }
  exact ⟨cert, rootReadUnary, consumerReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
