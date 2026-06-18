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

def AuditMapObstructionSocketCarrier [AskSetup] [PackageSetup]
    (audit positive conditional obstruction frontier transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  (∃ packet : AuditMapObstructionSocketUp,
      packet =
        AuditMapObstructionSocketUp.mk audit positive conditional obstruction frontier transport
          replay provenance localName) ∧
    UnaryHistory audit ∧ UnaryHistory positive ∧ UnaryHistory conditional ∧
      UnaryHistory obstruction ∧ UnaryHistory frontier ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          hsame audit positive ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem AuditMapObstructionSocketCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {audit positive conditional obstruction frontier transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapObstructionSocketCarrier audit positive conditional obstruction frontier transport replay
        provenance localName bundle pkg ->
      Cont audit positive conditional ->
        Cont obstruction frontier replay ->
          PkgSig bundle provenance pkg ->
            SemanticNameCert
                  (fun row : BHist => hsame row audit ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row positive ∨ hsame row conditional ∨ hsame row obstruction ∨
                      hsame row frontier)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont audit positive conditional ∧
                      Cont obstruction frontier replay ∧ PkgSig bundle provenance pkg)
                  hsame ∧
              UnaryHistory audit ∧ UnaryHistory positive ∧ UnaryHistory conditional ∧
                UnaryHistory obstruction ∧ UnaryHistory frontier := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier auditPositiveRoute obstructionFrontierRoute provenancePkg
  obtain ⟨_packetWitness, auditUnary, positiveUnary, conditionalUnary, obstructionUnary,
    frontierUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    auditPositiveSame, _provenancePkgCarrier, _localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row audit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row positive ∨ hsame row conditional ∨ hsame row obstruction ∨
              hsame row frontier)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont audit positive conditional ∧
              Cont obstruction frontier replay ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro audit ⟨hsame_refl audit, auditUnary⟩
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
      exact Or.inl (hsame_trans source.left auditPositiveSame)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditPositiveRoute, obstructionFrontierRoute, provenancePkg⟩
  }
  exact
    ⟨cert, auditUnary, positiveUnary, conditionalUnary, obstructionUnary, frontierUnary⟩

end BEDC.Derived.AuditMapObstructionSocketUp
