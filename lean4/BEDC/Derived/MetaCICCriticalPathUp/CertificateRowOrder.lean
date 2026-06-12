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

theorem MetaCICCriticalPathCertificateRowOrder [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName routeRead certificateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName routeRead →
        Cont routeRead transport certificateRead →
          PkgSig bundle certificateRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row certificateRead ∨ hsame row obstruction ∨
                    hsame row dischargeSocket) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                    hsame row dischargeSocket ∨ hsame row transport ∨ hsame row route ∨
                      hsame row localName ∨ hsame row routeRead ∨
                        hsame row certificateRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont route localName routeRead ∧
                    Cont routeRead transport certificateRead ∧
                      PkgSig bundle certificateRead pkg ∧ PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory routeRead ∧ UnaryHistory certificateRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalRead routeTransportCertificate certificatePkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalRead
  have certificateReadUnary : UnaryHistory certificateRead :=
    unary_cont_closed routeReadUnary transportUnary routeTransportCertificate
  have sourceCertificate :
      (fun row : BHist =>
        (hsame row certificateRead ∨ hsame row obstruction ∨ hsame row dischargeSocket) ∧
          UnaryHistory row) certificateRead := by
    exact ⟨Or.inl (hsame_refl certificateRead), certificateReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row certificateRead ∨ hsame row obstruction ∨ hsame row dischargeSocket) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row dischargeSocket ∨ hsame row transport ∨ hsame row route ∨
                hsame row localName ∨ hsame row routeRead ∨ hsame row certificateRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route localName routeRead ∧
              Cont routeRead transport certificateRead ∧ PkgSig bundle certificateRead pkg ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro certificateRead sourceCertificate
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
          | inl sameCertificate =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameCertificate)
          | inr rest =>
              cases rest with
              | inl sameObstruction =>
                  exact Or.inr (Or.inl
                    (hsame_trans (hsame_symm sameRows) sameObstruction))
              | inr sameSocket =>
                  exact Or.inr (Or.inr
                    (hsame_trans (hsame_symm sameRows) sameSocket))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCertificate =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr sameCertificate)))))))
      | inr rest =>
          cases rest with
          | inl sameObstruction =>
              exact Or.inr (Or.inr (Or.inl sameObstruction))
          | inr sameSocket =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameSocket)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeLocalRead, routeTransportCertificate, certificatePkg,
          provenancePkg⟩
  }
  exact ⟨cert, routeReadUnary, certificateReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
