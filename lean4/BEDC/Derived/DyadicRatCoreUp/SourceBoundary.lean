import BEDC.Derived.DyadicRatCoreUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DyadicRatCoreSourceBoundary_semanticNameCert
    {mantissa exponent ledger provenance : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              DyadicRatCoreCarrier mantissa exponent e provenance ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              DyadicRatCoreCarrier mantissa exponent e provenance ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              DyadicRatCoreCarrier mantissa exponent e provenance ∧ hsame row e)
          hsame ∧
        RatHistoryCarrier mantissa ∧ PositiveUnaryDenominator exponent ∧
          UnaryHistory ledger ∧ UnaryHistory provenance := by
  intro carrier
  let SourceSpec : BHist -> Prop :=
    fun row : BHist =>
      exists e : BHist, DyadicRatCoreCarrier mantissa exponent e provenance ∧ hsame row e
  have ledgerSource : SourceSpec ledger :=
    Exists.intro ledger (And.intro carrier (hsame_refl ledger))
  have cert : SemanticNameCert SourceSpec SourceSpec SourceSpec hsame := {
    core := {
      carrier_inhabited := Exists.intro ledger ledgerSource
      equiv_refl := by
        intro row _rowSource
        exact hsame_refl row
      equiv_symm := by
        intro _row _other rowOther
        exact hsame_symm rowOther
      equiv_trans := by
        intro _row _middle _other rowMiddle middleOther
        exact hsame_trans rowMiddle middleOther
      carrier_respects_equiv := by
        intro row other rowOther rowSource
        cases rowSource with
        | intro e rowWitness =>
            exact Exists.intro e
              (And.intro rowWitness.left
                (hsame_trans (hsame_symm rowOther) rowWitness.right))
    }
    pattern_sound := by
      intro _row rowSource
      exact rowSource
    ledger_sound := by
      intro _row rowSource
      exact rowSource
  }
  exact And.intro cert
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.right.right carrier.right.right.left)))

end BEDC.Derived.DyadicRatCoreUp
