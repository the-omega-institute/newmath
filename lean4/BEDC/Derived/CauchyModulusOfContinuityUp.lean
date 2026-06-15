import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusOfContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusOfContinuityCarrier [AskSetup] [PackageSetup]
    (source target modulus transformer readback realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory modulus ∧
    UnaryHistory transformer ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        Cont modulus source transformer ∧ Cont transformer target readback ∧
          Cont readback realSeal localName ∧ Cont transport replay provenance ∧
            PkgSig bundle localName pkg

theorem CauchyModulusOfContinuityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source target modulus transformer readback realSeal transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusOfContinuityCarrier source target modulus transformer readback realSeal
        transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row modulus ∨
              hsame row transformer ∨ hsame row readback ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus source transformer ∧
              Cont transformer target readback ∧ Cont readback realSeal localName ∧
                PkgSig bundle localName pkg)
          hsame ∧
        UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨_sourceUnary, _targetUnary, _modulusUnary, _transformerUnary, _readbackUnary,
    realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, modulusSourceTransformer,
    transformerTargetReadback, readbackRealSealLocalName, _transportReplayProvenance,
    localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row modulus ∨
              hsame row transformer ∨ hsame row readback ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus source transformer ∧
              Cont transformer target readback ∧ Cont readback realSeal localName ∧
                PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, modulusSourceTransformer, transformerTargetReadback,
            readbackRealSealLocalName, localNamePkg⟩
    }
  exact ⟨cert, realSealUnary⟩

theorem CauchyModulusOfContinuityCarrier_cauchy_continuous_map_threshold_handoff
    [AskSetup] [PackageSetup]
    {source target modulus transformer readback realSeal transport replay provenance
      localName targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusOfContinuityCarrier source target modulus transformer readback realSeal
        transport replay provenance localName bundle pkg ->
      Cont modulus source targetRead ->
        PkgSig bundle targetRead pkg ->
          UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory transformer ∧
            UnaryHistory targetRead ∧ Cont modulus source transformer ∧
              Cont modulus source targetRead ∧ Cont transformer target readback ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier targetReadRoute targetReadPkg
  obtain ⟨sourceUnary, _targetUnary, modulusUnary, transformerUnary, _readbackUnary,
    _realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    modulusSourceTransformer, transformerTargetReadback, _readbackRealSealLocalName,
    _transportReplayProvenance, localNamePkg⟩ := carrier
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed modulusUnary sourceUnary targetReadRoute
  exact
    ⟨sourceUnary, modulusUnary, transformerUnary, targetReadUnary,
      modulusSourceTransformer, targetReadRoute, transformerTargetReadback, localNamePkg,
      targetReadPkg⟩

end BEDC.Derived.CauchyModulusOfContinuityUp
