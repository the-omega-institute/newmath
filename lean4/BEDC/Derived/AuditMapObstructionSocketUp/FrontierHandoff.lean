import BEDC.Derived.AuditMapObstructionSocketUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMapObstructionSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def audit_map_obstruction_socket_frontier_handoff_carrier [AskSetup] [PackageSetup]
    (auditTag positive conditional obstruction frontier transport continuations provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory auditTag ∧ UnaryHistory positive ∧ UnaryHistory conditional ∧
    UnaryHistory obstruction ∧ UnaryHistory frontier ∧ UnaryHistory transport ∧
      UnaryHistory continuations ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont frontier transport continuations ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle nameCert pkg

theorem AuditMapObstructionSocket_frontier_handoff [AskSetup] [PackageSetup]
    {auditTag positive conditional obstruction frontier transport continuations provenance
      nameCert frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    audit_map_obstruction_socket_frontier_handoff_carrier auditTag positive conditional obstruction frontier transport
        continuations provenance nameCert bundle pkg →
      Cont frontier transport frontierRead →
        SemanticNameCert
            (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row frontier ∨ hsame row transport ∨ hsame row continuations ∨
                hsame row provenance ∨ hsame row nameCert ∨ hsame row frontierRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont frontier transport frontierRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg)
            hsame ∧
          UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier frontierRoute
  obtain ⟨_auditUnary, _positiveUnary, _conditionalUnary, _obstructionUnary, frontierUnary,
    transportUnary, _continuationsUnary, _provenanceUnary, _nameCertUnary,
    _carrierFrontierRoute, provenancePkg, nameCertPkg⟩ := carrier
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed frontierUnary transportUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row transport ∨ hsame row continuations ∨
              hsame row provenance ∨ hsame row nameCert ∨ hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont frontier transport frontierRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierRoute, provenancePkg, nameCertPkg⟩
  }
  exact ⟨cert, frontierReadUnary⟩

end BEDC.Derived.AuditMapObstructionSocketUp
