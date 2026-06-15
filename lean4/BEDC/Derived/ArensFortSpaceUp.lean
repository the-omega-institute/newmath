import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ArensFortSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ArensFortSpaceCarrier [AskSetup] [PackageSetup]
    (grid special topology observable windows transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory grid ∧ UnaryHistory special ∧ UnaryHistory topology ∧
    UnaryHistory observable ∧ UnaryHistory windows ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont grid special topology ∧ Cont topology observable windows ∧
          Cont windows transport replay ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem ArensFortSpaceCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {grid special topology observable windows transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArensFortSpaceCarrier grid special topology observable windows transport replay provenance
        localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            ArensFortSpaceCarrier grid special topology observable windows transport replay
              provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            ArensFortSpaceCarrier grid special topology observable windows transport replay
              provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  have carrierSource :
      ArensFortSpaceCarrier grid special topology observable windows transport replay provenance
        localName bundle pkg :=
    carrier
  obtain ⟨_gridUnary, _specialUnary, _topologyUnary, _observableUnary, _windowsUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localUnary, _gridSpecialRoute,
    _observableWindowRoute, _replayRoute, _provenancePkg, localPkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨carrierSource, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport localUnary (hsame_symm source.right), localPkg⟩
  }

end BEDC.Derived.ArensFortSpaceUp
