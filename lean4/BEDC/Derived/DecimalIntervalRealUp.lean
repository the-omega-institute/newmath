import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive DecimalIntervalRealUp : Type where
  | mk
      (lower upper tolerance windows bracket readback realSeal locatedRow transport replay provenance
        name : BHist) : DecimalIntervalRealUp

namespace DecimalIntervalRealUp

def DecimalIntervalRealCarrier [AskSetup] [PackageSetup]
    (lower upper tolerance window bracket readback realSeal located transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory tolerance ∧ UnaryHistory window ∧
    UnaryHistory bracket ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
      UnaryHistory located ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont lower upper bracket ∧
          Cont bracket tolerance readback ∧ Cont readback realSeal located ∧
            hsame transport (append lower upper) ∧ PkgSig bundle provenance pkg ∧
              hsame readback provenance

theorem DecimalIntervalRealCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {lower upper tolerance window bracket readback realSeal located transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DecimalIntervalRealCarrier lower upper tolerance window bracket readback realSeal located
        transport replay provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DecimalIntervalRealCarrier lower upper tolerance window bracket readback realSeal
            located transport replay provenance localName bundle pkg ∧ hsame row readback)
        (fun row : BHist =>
          hsame row lower ∨ hsame row upper ∨ hsame row tolerance ∨ hsame row window ∨
            hsame row bracket ∨ hsame row readback ∨ hsame row realSeal ∨ hsame row located)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row provenance)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame SemanticNameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_lowerUnary, _upperUnary, _toleranceUnary, _windowUnary, _bracketUnary,
    _readbackUnary, _realSealUnary, _locatedUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _lowerUpper, _bracketTolerance, _readbackSeal,
    _transportSame, provenancePkg, readbackProvenance⟩ := carrier
  have sourceReadback :
      (fun row : BHist =>
          DecimalIntervalRealCarrier lower upper tolerance window bracket readback realSeal
            located transport replay provenance localName bundle pkg ∧ hsame row readback)
        readback := by
    exact ⟨carrierWitness, hsame_refl readback⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro readback sourceReadback
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
          ⟨source.left,
            hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inl source.right)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, hsame_trans source.right readbackProvenance⟩
  }

end DecimalIntervalRealUp

end BEDC.Derived
