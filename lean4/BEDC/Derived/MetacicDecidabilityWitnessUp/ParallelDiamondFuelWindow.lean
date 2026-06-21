import BEDC.Derived.MetacicDecidabilityWitnessUp.DecidabilityWitnessPublicExport

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetacicParallelDiamondFuelWindow [AskSetup] [PackageSetup]
    (T S B F R H C P N D : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  MetacicDecidabilityWitnessCarrier T S B F R H C P N bundle pkg ∧
    UnaryHistory D ∧ Cont B F D

theorem MetacicParallelDiamondFuelWindow_closure [AskSetup] [PackageSetup]
    {T S B F R H C P N D : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicParallelDiamondFuelWindow T S B F R H C P N D bundle pkg →
      UnaryHistory D ∧ Cont B F D ∧
        MetacicDecidabilityWitnessCarrier T S B F R H C P N bundle pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro window
  obtain ⟨carrier, _displayedDUnary, diamondRoute⟩ := window
  have carrierWitness :
      MetacicDecidabilityWitnessCarrier T S B F R H C P N bundle pkg :=
    carrier
  obtain ⟨_tUnary, _sUnary, bUnary, fUnary, _rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _provenancePkg, _namePkg, _packet⟩ := carrier
  have closedD : UnaryHistory D :=
    unary_cont_closed bUnary fUnary diamondRoute
  exact ⟨closedD, diamondRoute, carrierWitness⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
