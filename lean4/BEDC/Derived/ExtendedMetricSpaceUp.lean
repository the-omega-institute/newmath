import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ExtendedMetricSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ExtendedMetricSpaceCarrier [AskSetup] [PackageSetup]
    (P D F T M L H C G N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig NameCert
  UnaryHistory P ∧ UnaryHistory D ∧ UnaryHistory F ∧ UnaryHistory T ∧ UnaryHistory M ∧
    UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory G ∧ UnaryHistory N ∧
      PkgSig bundle G pkg ∧ PkgSig bundle N pkg

theorem ExtendedMetricSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {P D F T M L H C G N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ExtendedMetricSpaceCarrier P D F T M L H C G N bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          ExtendedMetricSpaceCarrier P D F T M L H C G N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          ExtendedMetricSpaceCarrier P D F T M L H C G N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          ExtendedMetricSpaceCarrier P D F T M L H C G N bundle pkg ∧ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert NameCert
  intro carrier
  have sourceN :
      ExtendedMetricSpaceCarrier P D F T M L H C G N bundle pkg ∧ hsame N N :=
    ⟨carrier, hsame_refl N⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro N sourceN
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
        intro row other sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.ExtendedMetricSpaceUp
