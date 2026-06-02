import BEDC.Derived.RiemannStieltjesUp.TasteGate

namespace BEDC.Derived.RiemannStieltjesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannStieltjesCarrier_tagged_partition_induction [AskSetup] [PackageSetup]
    {F A T S I E H C P N baseCell refinedCell stepRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannStieltjesCarrier F A T S I E H C P N bundle pkg →
      Cont T S baseCell →
        Cont baseCell A refinedCell →
          Cont refinedCell I stepRead →
            Cont stepRead E handoffRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  UnaryHistory baseCell ∧ UnaryHistory refinedCell ∧
                    UnaryHistory stepRead ∧ UnaryHistory handoffRead ∧
                      Cont T S baseCell ∧ Cont baseCell A refinedCell ∧
                        Cont refinedCell I stepRead ∧ Cont stepRead E handoffRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier taggedPartitionRoute variationRefinementRoute stepRoute handoffRoute
    provenancePkg namePkg
  obtain ⟨_fUnary, aUnary, tUnary, sUnary, iUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _carrierTaggedRoute, _carrierHandoffRoute, _carrierReplayRoute,
    _carrierNamePkg⟩ := carrier
  have baseCellUnary : UnaryHistory baseCell :=
    unary_cont_closed tUnary sUnary taggedPartitionRoute
  have refinedCellUnary : UnaryHistory refinedCell :=
    unary_cont_closed baseCellUnary aUnary variationRefinementRoute
  have stepReadUnary : UnaryHistory stepRead :=
    unary_cont_closed refinedCellUnary iUnary stepRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed stepReadUnary eUnary handoffRoute
  exact
    ⟨baseCellUnary, refinedCellUnary, stepReadUnary, handoffReadUnary,
      taggedPartitionRoute, variationRefinementRoute, stepRoute, handoffRoute,
      provenancePkg, namePkg⟩

end BEDC.Derived.RiemannStieltjesUp
