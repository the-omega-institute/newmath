import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyTailComparisonCarrier [AskSetup] [PackageSetup]
    (x y modulus window endpoint readback provenance namecert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory x ∧
    UnaryHistory y ∧
      UnaryHistory modulus ∧
        UnaryHistory window ∧
          UnaryHistory endpoint ∧
            UnaryHistory readback ∧
              Cont x y modulus ∧
                Cont modulus window endpoint ∧
                  Cont endpoint readback provenance ∧
                    PkgSig bundle provenance pkg ∧ hsame namecert provenance

theorem CauchyTailComparisonCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {x y modulus window endpoint readback provenance namecert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCarrier x y modulus window endpoint readback provenance namecert
      bundle pkg ->
    SemanticNameCert
      (fun row : BHist =>
        CauchyTailComparisonCarrier x y modulus window endpoint readback provenance
          namecert bundle pkg ∧ hsame row provenance)
      (fun row : BHist =>
        CauchyTailComparisonCarrier x y modulus window endpoint readback provenance
          namecert bundle pkg ∧ hsame row provenance)
      (fun row : BHist =>
        CauchyTailComparisonCarrier x y modulus window endpoint readback provenance
          namecert bundle pkg ∧ hsame row provenance)
      hsame := by
  intro carrier
  exact
    { core :=
        { carrier_inhabited := Exists.intro provenance (And.intro carrier (hsame_refl provenance))
          equiv_refl := by
            intro h _source
            exact hsame_refl h
          equiv_symm := by
            intro h k same
            exact hsame_symm same
          equiv_trans := by
            intro h k r sameHK sameKR
            exact hsame_trans sameHK sameKR
          carrier_respects_equiv := by
            intro h k same sourceH
            exact And.intro sourceH.left (hsame_trans (hsame_symm same) sourceH.right) }
      pattern_sound := by
        intro _h source
        exact source
      ledger_sound := by
        intro _h source
        exact source }

end BEDC.Derived.CauchyTailComparisonUp
