import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Ext
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClassifierMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def ClassifierMorphismPacket [AskSetup] [PackageSetup]
    (source target graph extPreservation sigPreservation contPreservation transport
      provenance nameCert : BHist)
    (mark : BMark) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
    UnaryHistory extPreservation ∧ UnaryHistory sigPreservation ∧
      UnaryHistory contPreservation ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Ext source mark extPreservation ∧
          SigRel bundle target sigPreservation ∧
            Cont extPreservation sigPreservation contPreservation ∧
              hsame transport contPreservation ∧ hsame provenance contPreservation ∧
                hsame nameCert contPreservation ∧ PkgSig bundle contPreservation pkg

theorem ClassifierMorphismPacket_ext_sigrel_preservation [AskSetup] [PackageSetup]
    {source target graph extPreservation sigPreservation contPreservation transport
      provenance nameCert extPreservation' sigPreservation' contPreservation' : BHist}
    {mark : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClassifierMorphismPacket source target graph extPreservation sigPreservation
        contPreservation transport provenance nameCert mark bundle pkg ->
      Ext source mark extPreservation' ->
        SigRel bundle target sigPreservation' ->
          Cont extPreservation' sigPreservation' contPreservation' ->
            hsame extPreservation extPreservation' ->
              hsame sigPreservation sigPreservation' ->
                hsame contPreservation contPreservation' ∧ UnaryHistory contPreservation' := by
  -- BEDC touchpoint anchor: BHist Ext SigRel Cont hsame UnaryHistory
  intro packet extRead sigRead contRead extSame sigSame
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _extUnary, _sigUnary, contUnary,
    _transportUnary, _provenanceUnary, _nameUnary, extRow, sigRow, contRow,
    _transportSame, _provenanceSame, _nameSame, _pkgRow⟩ := packet
  have extExact : hsame extPreservation extPreservation' :=
    ext_deterministic extRow extRead
  have sigExact : hsame sigPreservation sigPreservation' :=
    sigSame
  have contExact : hsame contPreservation contPreservation' := by
    cases extExact
    cases sigExact
    exact cont_deterministic contRow contRead
  have contUnary' : UnaryHistory contPreservation' := by
    cases contExact
    exact contUnary
  exact ⟨contExact, contUnary'⟩

theorem ClassifierMorphismPacket_composition_closure [AskSetup] [PackageSetup]
    {source middle target graphAB graphBD extAB sigB contAB extBD sigD contBD compositeGraph
      compositeCont transport provenance nameCert : BHist}
    {mark : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClassifierMorphismPacket source middle graphAB extAB sigB contAB transport provenance
        nameCert mark bundle pkg →
      ClassifierMorphismPacket middle target graphBD extBD sigD contBD transport provenance
        nameCert mark bundle pkg →
        Cont graphAB graphBD compositeGraph →
          Cont extAB sigD compositeCont →
            PkgSig bundle compositeCont pkg →
              ClassifierMorphismPacket source target compositeGraph extAB sigD compositeCont
                compositeCont compositeCont compositeCont mark bundle pkg := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg Ext SigRel Cont hsame UnaryHistory
  intro packetAB packetBD graphComposite contComposite compositePkg
  obtain ⟨sourceUnary, _middleUnaryAB, graphABUnary, extABUnary, _sigBUnary, _contABUnary,
    _transportABUnary, _provenanceABUnary, _nameABUnary, extABRow, _sigBRow, _contABRow,
    _transportABSame, _provenanceABSame, _nameABSame, _pkgAB⟩ := packetAB
  obtain ⟨_middleUnaryBD, targetUnary, graphBDUnary, _extBDUnary, sigDUnary, _contBDUnary,
    _transportBDUnary, _provenanceBDUnary, _nameBDUnary, _extBDRow, sigDRow, _contBDRow,
    _transportBDSame, _provenanceBDSame, _nameBDSame, _pkgBD⟩ := packetBD
  have compositeGraphUnary : UnaryHistory compositeGraph :=
    unary_cont_closed graphABUnary graphBDUnary graphComposite
  have compositeContUnary : UnaryHistory compositeCont :=
    unary_cont_closed extABUnary sigDUnary contComposite
  exact
    ⟨sourceUnary, targetUnary, compositeGraphUnary, extABUnary, sigDUnary, compositeContUnary,
      compositeContUnary, compositeContUnary, compositeContUnary, extABRow, sigDRow,
      contComposite, hsame_refl compositeCont, hsame_refl compositeCont,
      hsame_refl compositeCont, compositePkg⟩

theorem ClassifierMorphismPacket_preservation_nonescape_scope [AskSetup] [PackageSetup]
    {source target graph extPreservation sigPreservation contPreservation transport provenance
      nameCert publicRead : BHist}
    {mark : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClassifierMorphismPacket source target graph extPreservation sigPreservation
        contPreservation transport provenance nameCert mark bundle pkg →
      Cont contPreservation nameCert publicRead →
        UnaryHistory publicRead ∧ UnaryHistory contPreservation ∧
          hsame transport contPreservation ∧ hsame provenance contPreservation ∧
            hsame nameCert contPreservation ∧ PkgSig bundle contPreservation pkg := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet publicRoute
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _extUnary, _sigUnary, contUnary,
    _transportUnary, _provenanceUnary, nameUnary, _extRow, _sigRow, _contRow,
    transportSame, provenanceSame, nameSame, pkgRow⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed contUnary nameUnary publicRoute
  exact ⟨publicUnary, contUnary, transportSame, provenanceSame, nameSame, pkgRow⟩

end BEDC.Derived.ClassifierMorphismUp
