import BEDC.Derived.BanachAlgebraUp.CompletionProductNonescape

namespace BEDC.Derived.BanachAlgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachAlgebraCauchyProductStability [AskSetup] [PackageSetup]
    {ring norm banach productControl completionSeal transport replay provenance localName cauchyInput
      productRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BanachAlgebraCarrier ring norm banach productControl completionSeal transport replay
        provenance localName bundle pkg ->
      Cont banach completionSeal cauchyInput ->
        Cont cauchyInput productControl productRead ->
          Cont productRead replay exported ->
            PkgSig bundle exported pkg ->
              UnaryHistory cauchyInput ∧ UnaryHistory productRead ∧ UnaryHistory exported ∧
                Cont banach completionSeal cauchyInput ∧
                  Cont cauchyInput productControl productRead ∧
                    Cont productRead replay exported ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier cauchyRoute productRoute exportRoute exportedPkg
  obtain ⟨_ringUnary, _normUnary, banachUnary, productControlUnary, completionUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localNameUnary, _ringNormRoute,
    _completionRoute, _replayRoute, provenancePkg⟩ := carrier
  have cauchyUnary : UnaryHistory cauchyInput :=
    unary_cont_closed banachUnary completionUnary cauchyRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed cauchyUnary productControlUnary productRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed productReadUnary replayUnary exportRoute
  exact
    ⟨cauchyUnary, productReadUnary, exportedUnary, cauchyRoute, productRoute, exportRoute,
      provenancePkg, exportedPkg⟩

end BEDC.Derived.BanachAlgebraUp
