import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyMetricCarrier [AskSetup] [PackageSetup]
    (R0 R1 W D Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory R0 ∧ UnaryHistory R1 ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory Q ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont R0 R1 W ∧ Cont W D Q ∧ Cont Q E C ∧ Cont H C P ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg

theorem RegularCauchyMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {R0 R1 W D Q E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyMetricCarrier R0 R1 W D Q E H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyMetricCarrier R0 R1 W D Q E H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          RegularCauchyMetricCarrier R0 R1 W D Q E H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          RegularCauchyMetricCarrier R0 R1 W D Q E H C P N bundle pkg ∧ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨carrier, hsame_refl N⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.RegularCauchyMetricUp
