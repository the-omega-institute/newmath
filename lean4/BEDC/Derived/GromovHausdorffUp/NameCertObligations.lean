import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GromovHausdorffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GromovHausdorffCarrier [AskSetup] [PackageSetup]
    (X Y KX KY R D H Q U T C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame NameCert
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory KX ∧ UnaryHistory KY ∧
    UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory H ∧ UnaryHistory Q ∧
      UnaryHistory U ∧ UnaryHistory T ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ Cont X Y R ∧ Cont KX KY D ∧ Cont R D H ∧
          Cont H Q U ∧ Cont U T C ∧ hsame C N ∧ PkgSig bundle P pkg ∧
            PkgSig bundle N pkg

theorem GromovHausdorffCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X Y KX KY R D H Q U T C P N : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    GromovHausdorffCarrier X Y KX KY R D H Q U T C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          GromovHausdorffCarrier X Y KX KY R D H Q U T C P N bundle pkg ∧
            hsame row N)
        (fun row : BHist =>
          GromovHausdorffCarrier X Y KX KY R D H Q U T C P N bundle pkg ∧
            hsame row N)
        (fun row : BHist =>
          GromovHausdorffCarrier X Y KX KY R D H Q U T C P N bundle pkg ∧
            hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert NameCert hsame Cont
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨carrier, hsame_refl N⟩
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
        exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

end BEDC.Derived.GromovHausdorffUp
