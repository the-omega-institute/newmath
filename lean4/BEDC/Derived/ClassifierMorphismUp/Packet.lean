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

end BEDC.Derived.ClassifierMorphismUp
