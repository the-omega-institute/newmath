import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRegularizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyRegularizationFiniteCarrier [AskSetup] [PackageSetup]
    (stream modulus dyadic window regseq realSeal sameRows route provenance namecert endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧
    UnaryHistory modulus ∧
    UnaryHistory dyadic ∧
    UnaryHistory window ∧
    UnaryHistory regseq ∧
    UnaryHistory realSeal ∧
    UnaryHistory sameRows ∧
    UnaryHistory route ∧
    UnaryHistory provenance ∧
    UnaryHistory namecert ∧
    UnaryHistory endpoint ∧
    Cont stream modulus dyadic ∧
    Cont dyadic window regseq ∧
    Cont regseq realSeal endpoint ∧
    hsame sameRows (append stream modulus) ∧
    hsame route (append dyadic window) ∧
    hsame provenance (append regseq realSeal) ∧
    hsame namecert endpoint ∧
    PkgSig bundle endpoint pkg

theorem CauchyRegularizationFiniteCarrier_namecert_obligation_surface [AskSetup]
    [PackageSetup]
    {stream modulus dyadic window regseq realSeal sameRows route provenance namecert endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRegularizationFiniteCarrier stream modulus dyadic window regseq realSeal sameRows route
      provenance namecert endpoint bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyRegularizationFiniteCarrier stream modulus dyadic window regseq realSeal sameRows
            route provenance namecert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyRegularizationFiniteCarrier stream modulus dyadic window regseq realSeal sameRows
            route provenance namecert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyRegularizationFiniteCarrier stream modulus dyadic window regseq realSeal sameRows
            route provenance namecert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier rfl)
      equiv_refl := by
        intro h _source
        rfl
      equiv_symm := by
        intro h k same
        exact same.symm
      equiv_trans := by
        intro h k r left right
        exact left.trans right
      carrier_respects_equiv := by
        intro h k same source
        exact And.intro source.left (same.symm.trans source.right)
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

end BEDC.Derived.CauchyRegularizationUp
