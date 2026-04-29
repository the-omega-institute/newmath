import BEDC.FKernel.Gap

/-! Typed naming certificates license derived interfaces through five certified fields. -/
namespace BEDC.FKernel.NameCert


axiom DerivedName : Type
axiom SourceSpec : Type
axiom PatternSpec : Type
axiom ClassifierSpec : Type
axiom StabilityCert : Type
axiom LedgerPolicy : Type

structure NameCert (N : DerivedName) : Type where
  sourceSpec : SourceSpec
  patternSpec : PatternSpec
  classifierSpec : ClassifierSpec
  stabilityCert : StabilityCert
  ledgerPolicy : LedgerPolicy

end BEDC.FKernel.NameCert
