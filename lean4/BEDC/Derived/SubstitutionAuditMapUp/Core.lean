import BEDC.Derived.SubstitutionAuditMapUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubstitutionAuditMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubstitutionAuditMapCarrier [AskSetup] [PackageSetup]
    (term closed shift substitute composition generator transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory term ∧ UnaryHistory closed ∧ UnaryHistory shift ∧ UnaryHistory substitute ∧
    UnaryHistory composition ∧ UnaryHistory generator ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        hsame term closed ∧ hsame shift substitute ∧ hsame composition generator ∧
          hsame transport route ∧ hsame provenance name ∧ hsame name generator ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem SubstitutionAuditMapCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          SubstitutionAuditMapCarrier term closed shift substitute composition generator transport
            route provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist => hsame row generator ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row name)
        hsame ∧ UnaryHistory term ∧ UnaryHistory closed ∧ UnaryHistory shift ∧
          UnaryHistory substitute ∧ UnaryHistory composition ∧ UnaryHistory generator ∧
            PkgSig bundle provenance pkg := by
  intro carrier
  have carrierWitness := carrier
  obtain ⟨termUnary, closedUnary, shiftUnary, substituteUnary, compositionUnary,
    generatorUnary, _transportUnary, _routeUnary, _provenanceUnary, nameUnary,
    _termClosed, _shiftSubstitute, _compositionGenerator, _transportRoute, _provenanceName,
    nameGenerator, provenancePkg, _namePkg⟩ := carrier
  have sourceName :
      (fun row : BHist =>
        SubstitutionAuditMapCarrier term closed shift substitute composition generator transport
          route provenance name bundle pkg ∧ hsame row name)
        name := by
    exact And.intro carrierWitness (hsame_refl name)
  have core :
      NameCert
        (fun row : BHist =>
          SubstitutionAuditMapCarrier term closed shift substitute composition generator
            transport route provenance name bundle pkg ∧ hsame row name)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro name sourceName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowName : hsame row name := sourceRow.right
        have sameOtherName : hsame other name :=
          hsame_trans (hsame_symm same) sameRowName
        exact And.intro sourceRow.left sameOtherName
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          SubstitutionAuditMapCarrier term closed shift substitute composition generator
            transport route provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist => hsame row generator ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row name)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row sourceRow
        have rowGenerator : hsame row generator :=
          hsame_trans sourceRow.right nameGenerator
        have rowUnary : UnaryHistory row :=
          unary_transport nameUnary (hsame_symm sourceRow.right)
        exact And.intro rowGenerator rowUnary
      ledger_sound := by
        intro row sourceRow
        exact And.intro provenancePkg sourceRow.right
    }
  exact
    ⟨cert, termUnary, closedUnary, shiftUnary, substituteUnary, compositionUnary,
      generatorUnary, provenancePkg⟩

end BEDC.Derived.SubstitutionAuditMapUp
