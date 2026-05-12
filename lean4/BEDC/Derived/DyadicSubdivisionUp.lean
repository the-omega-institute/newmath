import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicSubdivisionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicSubdivisionSource [AskSetup] [PackageSetup]
    (parent level cells mesh validated provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory parent ∧ UnaryHistory level ∧ UnaryHistory cells ∧ UnaryHistory mesh ∧
    UnaryHistory validated ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
      Cont parent level cells ∧ Cont cells mesh validated ∧
        Cont validated provenance name ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle name pkg

theorem DyadicSubdivisionSource_namecert_obligations [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {parent level cells mesh validated provenance name : BHist} :
    DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ∧
            hsame row validated)
        (fun row : BHist =>
          DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ∧
            hsame row validated)
        (fun row : BHist =>
          DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ∧
            hsame row validated)
        hsame := by
  intro sourceCarrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro validated (And.intro sourceCarrier (hsame_refl validated))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

def DyadicSubdivisionPacket [AskSetup] [PackageSetup]
    (parent level cells mesh validation provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory parent ∧ UnaryHistory level ∧ UnaryHistory cells ∧
    UnaryHistory provenance ∧ UnaryHistory name ∧ Cont level cells mesh ∧
      Cont mesh validation provenance ∧ PkgSig bundle provenance pkg

theorem DyadicSubdivisionPacket_refinement_stability [AskSetup] [PackageSetup]
    {parent level cells mesh validation provenance name parent' level' cells' mesh' validation'
      provenance' name' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionPacket parent level cells mesh validation provenance name bundle pkg ->
      hsame parent parent' -> hsame level level' -> hsame cells cells' ->
        hsame provenance provenance' -> hsame name name' -> Cont level' cells' mesh' ->
          Cont mesh' validation' provenance' -> PkgSig bundle provenance' pkg ->
            DyadicSubdivisionPacket parent' level' cells' mesh' validation' provenance' name'
              bundle pkg /\ hsame mesh mesh' /\ hsame validation validation' := by
  -- BEDC touchpoint anchor: BHist
  intro packet parentSame levelSame cellsSame provenanceSame nameSame refinedMesh
    refinedValidation refinedPkg
  have parentUnary : UnaryHistory parent := packet.left
  have levelUnary : UnaryHistory level := packet.right.left
  have cellsUnary : UnaryHistory cells := packet.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.left
  have nameUnary : UnaryHistory name := packet.right.right.right.right.left
  have meshCont : Cont level cells mesh := packet.right.right.right.right.right.left
  have validationCont : Cont mesh validation provenance :=
    packet.right.right.right.right.right.right.left
  have parentUnary' : UnaryHistory parent' := unary_transport parentUnary parentSame
  have levelUnary' : UnaryHistory level' := unary_transport levelUnary levelSame
  have cellsUnary' : UnaryHistory cells' := unary_transport cellsUnary cellsSame
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary provenanceSame
  have nameUnary' : UnaryHistory name' := unary_transport nameUnary nameSame
  have meshSame : hsame mesh mesh' :=
    cont_respects_hsame levelSame cellsSame meshCont refinedMesh
  have validationSame : hsame validation validation' := by
    cases meshSame
    cases provenanceSame
    exact cont_left_cancel validationCont refinedValidation
  constructor
  · constructor
    · exact parentUnary'
    · constructor
      · exact levelUnary'
      · constructor
        · exact cellsUnary'
        · constructor
          · exact provenanceUnary'
          · constructor
            · exact nameUnary'
            · constructor
              · exact refinedMesh
              · constructor
                · exact refinedValidation
                · exact refinedPkg
  · constructor
    · exact meshSame
    · exact validationSame

theorem DyadicSubdivisionSource_mesh_coverage [AskSetup] [PackageSetup]
    {parent level cells mesh validated provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg →
      UnaryHistory parent ∧
        UnaryHistory level ∧
        UnaryHistory cells ∧
        UnaryHistory mesh ∧
        UnaryHistory validated ∧
        UnaryHistory provenance ∧
        UnaryHistory name ∧
        Cont parent level cells ∧
        Cont cells mesh validated ∧
        Cont validated provenance name ∧
        PkgSig bundle provenance pkg ∧
        PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro source
  cases source with
  | intro parentUnary rest =>
      cases rest with
      | intro levelUnary rest =>
          cases rest with
          | intro cellsUnary rest =>
              cases rest with
              | intro meshUnary rest =>
                  cases rest with
                  | intro validatedUnary rest =>
                      cases rest with
                      | intro provenanceUnary rest =>
                          cases rest with
                          | intro nameUnary rest =>
                              cases rest with
                              | intro parentLevelCont rest =>
                                  cases rest with
                                  | intro cellsMeshCont rest =>
                                      cases rest with
                                      | intro validatedProvenanceCont rest =>
                                          cases rest with
                                          | intro provenancePkg namePkg =>
                                              constructor
                                              · exact parentUnary
                                              constructor
                                              · exact levelUnary
                                              constructor
                                              · exact cellsUnary
                                              constructor
                                              · exact meshUnary
                                              constructor
                                              · exact validatedUnary
                                              constructor
                                              · exact provenanceUnary
                                              constructor
                                              · exact nameUnary
                                              constructor
                                              · exact parentLevelCont
                                              constructor
                                              · exact cellsMeshCont
                                              constructor
                                              · exact validatedProvenanceCont
                                              constructor
                                              · exact provenancePkg
                                              exact namePkg

end BEDC.Derived.DyadicSubdivisionUp
