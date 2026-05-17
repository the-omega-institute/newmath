import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMapInterfaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def AuditMapInterfaceCarrier [AskSetup] [PackageSetup]
    (established conditional obstruction frontier crossMap transport route provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory established ∧ UnaryHistory conditional ∧ UnaryHistory obstruction ∧
    UnaryHistory frontier ∧ UnaryHistory crossMap ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont established conditional obstruction ∧ Cont obstruction frontier crossMap ∧
          Cont transport route provenance ∧ PkgSig bundle localCert pkg

theorem AuditMapInterfaceCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {established conditional obstruction frontier crossMap transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport route
        provenance localCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport
              route provenance localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            Cont established conditional obstruction ∧ Cont obstruction frontier crossMap ∧
              Cont transport route provenance ∧ hsame row localCert)
          (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
          hsame ∧
        UnaryHistory established ∧ UnaryHistory conditional ∧ UnaryHistory obstruction ∧
          UnaryHistory frontier ∧ UnaryHistory crossMap ∧ UnaryHistory transport ∧
            UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
              Cont established conditional obstruction ∧ Cont obstruction frontier crossMap ∧
                Cont transport route provenance ∧ PkgSig bundle localCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨establishedUnary, conditionalUnary, obstructionUnary, frontierUnary, crossMapUnary,
    transportUnary, routeUnary, provenanceUnary, localCertUnary, establishedConditionalObstruction,
    obstructionFrontierCrossMap, transportRouteProvenance, localCertPkg⟩ := carrier
  have certCore :
      NameCert
        (fun row : BHist =>
          AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport
            route provenance localCert bundle pkg ∧ hsame row localCert)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro localCert
        (And.intro carrierWitness (hsame_refl localCert))
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
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport
              route provenance localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            Cont established conditional obstruction ∧ Cont obstruction frontier crossMap ∧
              Cont transport route provenance ∧ hsame row localCert)
          (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨establishedConditionalObstruction, obstructionFrontierCrossMap,
            transportRouteProvenance, sourceRow.right⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨localCertPkg, sourceRow.right⟩
    }
  exact
    ⟨semantic, establishedUnary, conditionalUnary, obstructionUnary, frontierUnary, crossMapUnary,
      transportUnary, routeUnary, provenanceUnary, localCertUnary, establishedConditionalObstruction,
        obstructionFrontierCrossMap, transportRouteProvenance, localCertPkg⟩

end BEDC.Derived.AuditMapInterfaceUp
