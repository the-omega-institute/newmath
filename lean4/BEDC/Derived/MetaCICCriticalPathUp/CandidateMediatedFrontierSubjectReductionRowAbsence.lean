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

theorem MetaCICCriticalPathCandidateMediatedFrontierSubjectReductionRowAbsence
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName subjectRow socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont normalForm dischargeSocket socketRead ->
        Cont socketRead subjectRow subjectRow ->
          PkgSig bundle socketRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row socketRead ∨ hsame row dischargeSocket ∨ hsame row subjectRow) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row dischargeSocket ∨
                    hsame row socketRead ∨ hsame row subjectRow)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                    Cont normalForm dischargeSocket socketRead)
                hsame ∧
              UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet normalSocketRead _subjectRoute socketPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed normalFormUnary dischargeSocketUnary normalSocketRead
  have sourceSocket :
      (fun row : BHist =>
        (hsame row socketRead ∨ hsame row dischargeSocket ∨ hsame row subjectRow) ∧
          UnaryHistory row) socketRead := by
    exact ⟨Or.inl (hsame_refl socketRead), socketUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row socketRead ∨ hsame row dischargeSocket ∨ hsame row subjectRow) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row dischargeSocket ∨
              hsame row socketRead ∨ hsame row subjectRow)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              Cont normalForm dischargeSocket socketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocket
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
        intro row other sameRows source
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        cases source.left with
        | inl sameSocket =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameSocket), otherUnary⟩
        | inr rest =>
            cases rest with
            | inl sameDischarge =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDischarge)),
                    otherUnary⟩
            | inr sameSubject =>
                exact
                  ⟨Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSubject)),
                    otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSocket =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameSocket)))
      | inr rest =>
          cases rest with
          | inl sameDischarge =>
              exact Or.inr (Or.inr (Or.inl sameDischarge))
          | inr sameSubject =>
              exact Or.inr (Or.inr (Or.inr (Or.inr sameSubject)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketPkg, normalSocketRead⟩
  }
  exact ⟨cert, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
