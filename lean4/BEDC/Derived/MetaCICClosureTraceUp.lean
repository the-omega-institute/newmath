import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICClosureTraceCarrier [AskSetup] [PackageSetup]
    (S U V B R G K H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory B ∧
    UnaryHistory R ∧ UnaryHistory G ∧ UnaryHistory K ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont S U V ∧
        Cont V G K ∧ Cont B R C ∧ PkgSig bundle P pkg

theorem MetaCICClosureTraceCarrier_substitution_shift_generator_package
    [AskSetup] [PackageSetup] {S U V B R G K H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory G ∧
        Cont S U V ∧ Cont V G K ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨SUnary, UUnary, VUnary, _BUnary, _RUnary, GUnary, _KUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, shiftSubstitution, generatorPackage, _betaRoute,
    pkgSig⟩ := carrier
  exact ⟨SUnary, UUnary, VUnary, GUnary, shiftSubstitution, generatorPackage, pkgSig⟩

end BEDC.Derived.MetaCICClosureTraceUp
