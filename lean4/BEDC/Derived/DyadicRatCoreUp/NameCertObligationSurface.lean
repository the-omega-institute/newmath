import BEDC.Derived.DyadicRatCoreUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DyadicRatCoreCarrier_namecert_obligation_surface
    {mantissa exponent ledger provenance : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      SemanticNameCert
          (fun row : BHist => exists l : BHist, DyadicRatCoreCarrier mantissa exponent l row)
          (fun row : BHist => exists l : BHist, DyadicRatCoreCarrier mantissa exponent l row)
          (fun row : BHist => exists l : BHist, DyadicRatCoreCarrier mantissa exponent l row)
          hsame ∧
        RatHistoryCarrier mantissa ∧ PositiveUnaryDenominator exponent ∧ UnaryHistory ledger ∧
          Cont exponent mantissa ledger := by
  intro carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => exists l : BHist, DyadicRatCoreCarrier mantissa exponent l row)
          (fun row : BHist => exists l : BHist, DyadicRatCoreCarrier mantissa exponent l row)
          (fun row : BHist => exists l : BHist, DyadicRatCoreCarrier mantissa exponent l row)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance (Exists.intro ledger carrier)
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows rowCarrier
        cases rowCarrier with
        | intro l rowData =>
            have rowUnary' : UnaryHistory row' :=
              unary_transport rowData.right.right.left sameRows
            have transported : DyadicRatCoreCarrier mantissa exponent l row' :=
              And.intro rowData.left
                (And.intro rowData.right.left
                  (And.intro rowUnary'
                    (And.intro rowData.right.right.right.left
                      rowData.right.right.right.right)))
            exact Exists.intro l transported
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }
  exact And.intro cert
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.right.right carrier.right.right.right.left)))

end BEDC.Derived.DyadicRatCoreUp
