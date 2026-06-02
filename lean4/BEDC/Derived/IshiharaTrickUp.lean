import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive IshiharaTrickUp : Type where
  | mk :
      (schedule readback tolerance realSeal branchRow transport replay provenance localName : BHist) →
        IshiharaTrickUp
  deriving DecidableEq

end BEDC.Derived

namespace BEDC.Derived.IshiharaTrickUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IshiharaTrickCarrier [AskSetup] [PackageSetup]
    (S R T W D E A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory W ∧ UnaryHistory D ∧
    UnaryHistory E ∧ UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont S R T ∧ Cont W D A ∧ Cont T W E ∧ Cont H C P ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem IshiharaTrickCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S R T W D E A H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IshiharaTrickCarrier S R T W D E A H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          IshiharaTrickCarrier S R T W D E A H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          IshiharaTrickCarrier S R T W D E A H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          IshiharaTrickCarrier S R T W D E A H C P N bundle pkg ∧ hsame row N)
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

end BEDC.Derived.IshiharaTrickUp
