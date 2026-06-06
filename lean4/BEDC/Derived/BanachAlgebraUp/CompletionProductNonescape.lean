import BEDC.Derived.BanachAlgebraUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachAlgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BanachAlgebraCarrier [AskSetup] [PackageSetup]
    (ring norm banach productControl completionSeal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory ring ∧ UnaryHistory norm ∧ UnaryHistory banach ∧
    UnaryHistory productControl ∧ UnaryHistory completionSeal ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont ring norm banach ∧ Cont banach productControl completionSeal ∧
          Cont productControl completionSeal replay ∧ PkgSig bundle provenance pkg

theorem BanachAlgebraCompletionProductNonescape [AskSetup] [PackageSetup]
    {ring norm banach productControl completionSeal transport replay provenance localName
      productRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BanachAlgebraCarrier ring norm banach productControl completionSeal transport replay
        provenance localName bundle pkg →
      Cont productControl completionSeal productRead →
        Cont productRead replay exported →
          PkgSig bundle exported pkg →
            UnaryHistory productControl ∧ UnaryHistory completionSeal ∧
              UnaryHistory productRead ∧ UnaryHistory exported ∧
                Cont productControl completionSeal productRead ∧
                  Cont productRead replay exported ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier productRoute exportRoute exportedPkg
  obtain ⟨_ringUnary, _normUnary, _banachUnary, productUnary, completionUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localNameUnary, _ringNormRoute,
    _completionRoute, _replayRoute, provenancePkg⟩ := carrier
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed productUnary completionUnary productRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed productReadUnary replayUnary exportRoute
  exact
    ⟨productUnary, completionUnary, productReadUnary, exportedUnary, productRoute,
      exportRoute, provenancePkg, exportedPkg⟩

end BEDC.Derived.BanachAlgebraUp
