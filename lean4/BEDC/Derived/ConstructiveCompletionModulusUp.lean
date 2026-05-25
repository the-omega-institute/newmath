import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConstructiveCompletionModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive ConstructiveCompletionModulusUp : Type where
  | mk
      (source modulus window readback dyadic realSeal transport replay provenance name :
        BHist) :
      ConstructiveCompletionModulusUp
  deriving DecidableEq

def ConstructiveCompletionModulusCarrier [AskSetup] [PackageSetup]
    (source modulus window readback dyadic realSeal transport replay provenance name :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle name pkg

theorem ConstructiveCompletionModulusCarrier_namecert_obligations [AskSetup]
    [PackageSetup]
    {source modulus window readback dyadic realSeal transport replay provenance name :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConstructiveCompletionModulusCarrier source modulus window readback dyadic realSeal
        transport replay provenance name bundle pkg ->
      UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
        UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory realSeal ∧
          UnaryHistory transport ∧ UnaryHistory replay ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory
  intro carrier
  exact carrier

end BEDC.Derived.ConstructiveCompletionModulusUp
