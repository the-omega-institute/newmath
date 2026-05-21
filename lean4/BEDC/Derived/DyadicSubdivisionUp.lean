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

theorem DyadicSubdivisionSource_namecert_package [AskSetup] [PackageSetup]
    {parent level cells mesh validated provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ->
      Cont mesh validated endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory parent ∧ UnaryHistory level ∧ UnaryHistory cells ∧
            UnaryHistory mesh ∧ UnaryHistory validated ∧ Cont mesh validated endpoint ∧
              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro source meshValidatedEndpoint endpointPkg
  obtain ⟨parentUnary, levelUnary, cellsUnary, meshUnary, validatedUnary,
    _provenanceUnary, _nameUnary, _parentLevelCells, _cellsMeshValidated,
    _validatedProvenanceName, _provenancePkg, _namePkg⟩ := source
  exact
    ⟨parentUnary, levelUnary, cellsUnary, meshUnary, validatedUnary,
      meshValidatedEndpoint, endpointPkg⟩

theorem DyadicSubdivisionSource_validated_enclosure_handoff [AskSetup] [PackageSetup]
    {parent level cells mesh validated provenance name enclosure : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ->
      Cont mesh validated enclosure ->
        PkgSig bundle enclosure pkg ->
          UnaryHistory parent ∧ UnaryHistory level ∧ UnaryHistory cells ∧
            UnaryHistory mesh ∧ UnaryHistory validated ∧ UnaryHistory enclosure ∧
              Cont parent level cells ∧ Cont cells mesh validated ∧
                Cont mesh validated enclosure ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle enclosure pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro source enclosureRoute enclosurePkg
  obtain ⟨parentUnary, levelUnary, cellsUnary, meshUnary, validatedUnary, _provenanceUnary,
    _nameUnary, parentLevelCells, cellsMeshValidated, _validatedProvenanceName,
    _provenancePkg, namePkg⟩ := source
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed meshUnary validatedUnary enclosureRoute
  exact
    ⟨parentUnary, levelUnary, cellsUnary, meshUnary, validatedUnary, enclosureUnary,
      parentLevelCells, cellsMeshValidated, enclosureRoute, namePkg, enclosurePkg⟩

theorem DyadicSubdivisionSource_cell_ledger_transport [AskSetup] [PackageSetup]
    {parent level cells mesh validated provenance name parent' level' cells' mesh' validated'
      provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ->
      hsame parent parent' -> hsame level level' -> hsame cells cells' ->
        hsame mesh mesh' -> hsame validated validated' -> hsame provenance provenance' ->
          hsame name name' -> Cont parent' level' cells' -> Cont cells' mesh' validated' ->
            Cont validated' provenance' name' -> PkgSig bundle provenance' pkg ->
              PkgSig bundle name' pkg ->
                DyadicSubdivisionSource parent' level' cells' mesh' validated' provenance'
                  name' bundle pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro source parentSame levelSame cellsSame meshSame validatedSame provenanceSame nameSame
    parentLevelCells cellsMeshValidated validatedProvenanceName provenancePkg namePkg
  obtain ⟨parentUnary, levelUnary, cellsUnary, meshUnary, validatedUnary, provenanceUnary,
    nameUnary, _parentLevelCells, _cellsMeshValidated, _validatedProvenanceName,
    _provenancePkg, _namePkg⟩ := source
  have parentUnary' : UnaryHistory parent' := unary_transport parentUnary parentSame
  have levelUnary' : UnaryHistory level' := unary_transport levelUnary levelSame
  have cellsUnary' : UnaryHistory cells' := unary_transport cellsUnary cellsSame
  have meshUnary' : UnaryHistory mesh' := unary_transport meshUnary meshSame
  have validatedUnary' : UnaryHistory validated' :=
    unary_transport validatedUnary validatedSame
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary provenanceSame
  have nameUnary' : UnaryHistory name' := unary_transport nameUnary nameSame
  exact
    ⟨parentUnary', levelUnary', cellsUnary', meshUnary', validatedUnary', provenanceUnary',
      nameUnary', parentLevelCells, cellsMeshValidated, validatedProvenanceName,
      provenancePkg, namePkg⟩

theorem DyadicSubdivisionPacket_refinement_composition [AskSetup] [PackageSetup]
    {parent level cells mesh validation provenance name level' cells' mesh' validation'
      provenance' name' level'' cells'' mesh'' validation'' provenance'' name'' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionPacket parent level cells mesh validation provenance name bundle pkg ->
      hsame level level' -> hsame cells cells' -> hsame provenance provenance' ->
        hsame name name' -> Cont level' cells' mesh' ->
          Cont mesh' validation' provenance' -> PkgSig bundle provenance' pkg ->
            hsame level' level'' -> hsame cells' cells'' -> hsame provenance' provenance'' ->
              hsame name' name'' -> Cont level'' cells'' mesh'' ->
                Cont mesh'' validation'' provenance'' -> PkgSig bundle provenance'' pkg ->
                  DyadicSubdivisionPacket parent level'' cells'' mesh'' validation''
                    provenance'' name'' bundle pkg ∧
                    hsame mesh mesh'' ∧ hsame validation validation'' := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro packet levelSame cellsSame provenanceSame nameSame firstMesh firstValidation firstPkg
    levelSame' cellsSame' provenanceSame' nameSame' secondMesh secondValidation secondPkg
  have first :
      DyadicSubdivisionPacket parent level' cells' mesh' validation' provenance' name'
          bundle pkg ∧
        hsame mesh mesh' ∧ hsame validation validation' :=
    DyadicSubdivisionPacket_refinement_stability packet (hsame_refl parent) levelSame
      cellsSame provenanceSame nameSame firstMesh firstValidation firstPkg
  have second :
      DyadicSubdivisionPacket parent level'' cells'' mesh'' validation'' provenance'' name''
          bundle pkg ∧
        hsame mesh' mesh'' ∧ hsame validation' validation'' :=
    DyadicSubdivisionPacket_refinement_stability first.left (hsame_refl parent) levelSame'
      cellsSame' provenanceSame' nameSame' secondMesh secondValidation secondPkg
  exact
    ⟨second.left, hsame_trans first.right.left second.right.left,
      hsame_trans first.right.right second.right.right⟩

theorem DyadicSubdivisionSource_scoped_finite_route_package [AskSetup] [PackageSetup]
    -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
    {parent level cells mesh validated provenance name enclosureRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ->
      Cont validated name enclosureRead ->
        Cont enclosureRead provenance consumerRead ->
          PkgSig bundle enclosureRead pkg ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    DyadicSubdivisionSource parent level cells mesh validated provenance name
                        bundle pkg ∧
                      hsame row validated)
                  (fun row : BHist =>
                    DyadicSubdivisionSource parent level cells mesh validated provenance name
                        bundle pkg ∧
                      hsame row validated)
                  (fun row : BHist =>
                    DyadicSubdivisionSource parent level cells mesh validated provenance name
                        bundle pkg ∧
                      hsame row validated)
                  hsame ∧
                UnaryHistory parent ∧
                UnaryHistory level ∧
                UnaryHistory cells ∧
                UnaryHistory mesh ∧
                UnaryHistory validated ∧
                UnaryHistory enclosureRead ∧
                UnaryHistory consumerRead ∧
                Cont parent level cells ∧
                Cont cells mesh validated ∧
                Cont validated name enclosureRead ∧
                Cont enclosureRead provenance consumerRead ∧
                PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧
                PkgSig bundle enclosureRead pkg ∧
                PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro source validatedNameEnclosure enclosureProvenanceConsumer enclosurePkg consumerPkg
  have certSurface :=
    DyadicSubdivisionSource_namecert_obligations source
  obtain ⟨parentUnary, levelUnary, cellsUnary, meshUnary, validatedUnary,
    provenanceUnary, _nameUnary, parentLevelCells, cellsMeshValidated,
    _validatedProvenanceName, provenancePkg, namePkg⟩ := source
  have enclosureUnary : UnaryHistory enclosureRead :=
    unary_cont_closed validatedUnary _nameUnary validatedNameEnclosure
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed enclosureUnary provenanceUnary enclosureProvenanceConsumer
  exact
    ⟨certSurface,
      parentUnary,
      levelUnary,
      cellsUnary,
      meshUnary,
      validatedUnary,
      enclosureUnary,
      consumerUnary,
      parentLevelCells,
      cellsMeshValidated,
      validatedNameEnclosure,
      enclosureProvenanceConsumer,
      provenancePkg,
      namePkg,
      enclosurePkg,
      consumerPkg⟩

theorem DyadicSubdivisionPacket_common_refinement_exhaustion [AskSetup] [PackageSetup]
    {parent level0 cells0 mesh0 validation0 provenance0 name0 level1 cells1 mesh1
      validation1 provenance1 name1 levelCommon cellsCommon meshCommon validationCommon
      provenanceCommon nameCommon : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionPacket parent level0 cells0 mesh0 validation0 provenance0 name0
        bundle pkg ->
      DyadicSubdivisionPacket parent level1 cells1 mesh1 validation1 provenance1 name1
        bundle pkg ->
        hsame level0 levelCommon -> hsame cells0 cellsCommon ->
          hsame provenance0 provenanceCommon -> hsame name0 nameCommon ->
            hsame level1 levelCommon -> hsame cells1 cellsCommon ->
              hsame provenance1 provenanceCommon -> hsame name1 nameCommon ->
                Cont levelCommon cellsCommon meshCommon ->
                  Cont meshCommon validationCommon provenanceCommon ->
                    PkgSig bundle provenanceCommon pkg ->
                      DyadicSubdivisionPacket parent levelCommon cellsCommon meshCommon
                          validationCommon provenanceCommon nameCommon bundle pkg ∧
                        hsame mesh0 meshCommon ∧ hsame validation0 validationCommon ∧
                          hsame mesh1 meshCommon ∧ hsame validation1 validationCommon := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro leftPacket rightPacket levelSame0 cellsSame0 provenanceSame0 nameSame0 levelSame1
    cellsSame1 provenanceSame1 nameSame1 commonMesh commonValidation commonPkg
  have leftRefined :
      DyadicSubdivisionPacket parent levelCommon cellsCommon meshCommon validationCommon
          provenanceCommon nameCommon bundle pkg ∧
        hsame mesh0 meshCommon ∧ hsame validation0 validationCommon :=
    DyadicSubdivisionPacket_refinement_stability leftPacket (hsame_refl parent) levelSame0
      cellsSame0 provenanceSame0 nameSame0 commonMesh commonValidation commonPkg
  have rightRefined :
      DyadicSubdivisionPacket parent levelCommon cellsCommon meshCommon validationCommon
          provenanceCommon nameCommon bundle pkg ∧
        hsame mesh1 meshCommon ∧ hsame validation1 validationCommon :=
    DyadicSubdivisionPacket_refinement_stability rightPacket (hsame_refl parent) levelSame1
      cellsSame1 provenanceSame1 nameSame1 commonMesh commonValidation commonPkg
  exact
    ⟨leftRefined.left, leftRefined.right.left, leftRefined.right.right,
      rightRefined.right.left, rightRefined.right.right⟩

theorem DyadicSubdivisionSource_standard_bridge_certificate [AskSetup] [PackageSetup]
    {parent level cells mesh validated provenance name enclosureRead standardRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ->
      Cont mesh validated enclosureRead ->
        Cont enclosureRead provenance standardRead ->
          PkgSig bundle enclosureRead pkg ->
            PkgSig bundle standardRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    DyadicSubdivisionSource parent level cells mesh validated provenance name
                        bundle pkg ∧ hsame row validated)
                  (fun row : BHist =>
                    DyadicSubdivisionSource parent level cells mesh validated provenance name
                        bundle pkg ∧ hsame row validated)
                  (fun row : BHist =>
                    DyadicSubdivisionSource parent level cells mesh validated provenance name
                        bundle pkg ∧ hsame row validated)
                  hsame ∧
                UnaryHistory parent ∧ UnaryHistory level ∧ UnaryHistory cells ∧
                UnaryHistory mesh ∧ UnaryHistory validated ∧ UnaryHistory enclosureRead ∧
                UnaryHistory standardRead ∧ Cont parent level cells ∧
                Cont cells mesh validated ∧ Cont mesh validated enclosureRead ∧
                Cont enclosureRead provenance standardRead ∧ PkgSig bundle name pkg ∧
                PkgSig bundle enclosureRead pkg ∧ PkgSig bundle standardRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro source meshValidatedEnclosure enclosureProvenanceStandard enclosurePkg standardPkg
  have certSurface :=
    DyadicSubdivisionSource_namecert_obligations source
  obtain ⟨parentUnary, levelUnary, cellsUnary, meshUnary, validatedUnary, provenanceUnary,
    _nameUnary, parentLevelCells, cellsMeshValidated, _validatedProvenanceName,
    _provenancePkg, namePkg⟩ := source
  have enclosureUnary : UnaryHistory enclosureRead :=
    unary_cont_closed meshUnary validatedUnary meshValidatedEnclosure
  have standardUnary : UnaryHistory standardRead :=
    unary_cont_closed enclosureUnary provenanceUnary enclosureProvenanceStandard
  exact
    ⟨certSurface,
      parentUnary,
      levelUnary,
      cellsUnary,
      meshUnary,
      validatedUnary,
      enclosureUnary,
      standardUnary,
      parentLevelCells,
        cellsMeshValidated,
        meshValidatedEnclosure,
        enclosureProvenanceStandard,
        namePkg,
        enclosurePkg,
        standardPkg⟩

theorem DyadicSubdivisionSource_public_finite_enclosure_export [AskSetup] [PackageSetup]
    {parent level cells mesh validated provenance name enclosureRead realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ->
      Cont mesh validated enclosureRead ->
        Cont enclosureRead provenance realRead ->
          Cont realRead name publicRead ->
            PkgSig bundle enclosureRead pkg ->
              PkgSig bundle realRead pkg ->
                PkgSig bundle publicRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        DyadicSubdivisionSource parent level cells mesh validated provenance name
                          bundle pkg ∧ hsame row validated)
                      (fun row : BHist =>
                        DyadicSubdivisionSource parent level cells mesh validated provenance name
                          bundle pkg ∧ hsame row validated)
                      (fun row : BHist =>
                        DyadicSubdivisionSource parent level cells mesh validated provenance name
                          bundle pkg ∧ hsame row validated)
                      hsame ∧
                    UnaryHistory enclosureRead ∧ UnaryHistory realRead ∧
                      UnaryHistory publicRead ∧ Cont mesh validated enclosureRead ∧
                        Cont enclosureRead provenance realRead ∧ Cont realRead name publicRead ∧
                          PkgSig bundle enclosureRead pkg ∧ PkgSig bundle realRead pkg ∧
                            PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro source meshValidatedEnclosure enclosureProvenanceReal realNamePublic
    enclosurePkg realPkg publicPkg
  have certSurface :=
    DyadicSubdivisionSource_namecert_obligations source
  obtain ⟨_parentUnary, _levelUnary, _cellsUnary, meshUnary, validatedUnary, provenanceUnary,
    nameUnary, _parentLevelCells, _cellsMeshValidated, _validatedProvenanceName,
    _provenancePkg, _namePkg⟩ := source
  have enclosureUnary : UnaryHistory enclosureRead :=
    unary_cont_closed meshUnary validatedUnary meshValidatedEnclosure
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed enclosureUnary provenanceUnary enclosureProvenanceReal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realUnary nameUnary realNamePublic
  exact
    ⟨certSurface,
      enclosureUnary,
      realUnary,
      publicUnary,
      meshValidatedEnclosure,
      enclosureProvenanceReal,
      realNamePublic,
      enclosurePkg,
      realPkg,
      publicPkg⟩

theorem DyadicSubdivisionSource_routed_bisection_normal_form [AskSetup] [PackageSetup]
    {parent level cells mesh validated provenance name enclosureRead realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ->
      Cont mesh validated enclosureRead ->
        Cont enclosureRead provenance realRead ->
          Cont realRead name publicRead ->
            PkgSig bundle enclosureRead pkg ->
              PkgSig bundle realRead pkg ->
                PkgSig bundle publicRead pkg ->
                  UnaryHistory parent ∧ UnaryHistory level ∧ UnaryHistory cells ∧
                    UnaryHistory mesh ∧ UnaryHistory validated ∧ UnaryHistory enclosureRead ∧
                      UnaryHistory realRead ∧ UnaryHistory publicRead ∧
                        Cont parent level cells ∧ Cont cells mesh validated ∧
                          Cont mesh validated enclosureRead ∧
                            Cont enclosureRead provenance realRead ∧
                              Cont realRead name publicRead ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro source meshValidatedEnclosure enclosureProvenanceReal realNamePublic _enclosurePkg
    _realPkg publicPkg
  obtain ⟨parentUnary, levelUnary, cellsUnary, meshUnary, validatedUnary, provenanceUnary,
    nameUnary, parentLevelCells, cellsMeshValidated, _validatedProvenanceName, provenancePkg,
    namePkg⟩ := source
  have enclosureUnary : UnaryHistory enclosureRead :=
    unary_cont_closed meshUnary validatedUnary meshValidatedEnclosure
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed enclosureUnary provenanceUnary enclosureProvenanceReal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realUnary nameUnary realNamePublic
  exact
    ⟨parentUnary,
      levelUnary,
      cellsUnary,
      meshUnary,
      validatedUnary,
      enclosureUnary,
      realUnary,
      publicUnary,
      parentLevelCells,
      cellsMeshValidated,
      meshValidatedEnclosure,
      enclosureProvenanceReal,
      realNamePublic,
      provenancePkg,
      namePkg,
      publicPkg⟩

end BEDC.Derived.DyadicSubdivisionUp
