import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalNewtonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IntervalNewtonCarrier [AskSetup] [PackageSetup]
    (B F D N K V R H C P L : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory B ∧ UnaryHistory F ∧ UnaryHistory D ∧ UnaryHistory N ∧
    UnaryHistory K ∧ UnaryHistory V ∧ UnaryHistory R ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory L ∧ Cont V R L ∧
        PkgSig bundle L pkg

theorem IntervalNewtonKrawczykEnclosure [AskSetup] [PackageSetup]
    {B F D N K V R H C P L narrowed : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    IntervalNewtonCarrier B F D N K V R H C P L bundle pkg ->
      Cont N K narrowed ->
        PkgSig bundle narrowed pkg ->
          UnaryHistory B ∧ UnaryHistory N ∧ UnaryHistory K ∧ UnaryHistory V ∧
            UnaryHistory narrowed ∧ Cont N K narrowed ∧ PkgSig bundle L pkg ∧
              PkgSig bundle narrowed pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier narrowedRoute narrowedPkg
  obtain ⟨unaryB, _unaryF, _unaryD, unaryN, unaryK, unaryV, _unaryR, _unaryH,
    _unaryC, _unaryP, _unaryL, _validatedLocal, localPkg⟩ := carrier
  have unaryNarrowed : UnaryHistory narrowed :=
    unary_cont_closed unaryN unaryK narrowedRoute
  exact
    ⟨unaryB, unaryN, unaryK, unaryV, unaryNarrowed, narrowedRoute, localPkg, narrowedPkg⟩

end BEDC.Derived.IntervalNewtonUp
