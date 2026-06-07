import BEDC.Derived.BanachAlgebraUp.CompletionProductNonescape

namespace BEDC.Derived.BanachAlgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachAlgebraNormSubmultiplicativityLedger [AskSetup] [PackageSetup]
    {ring norm banach productControl completionSeal transport replay provenance localName normLedger
      productRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BanachAlgebraCarrier ring norm banach productControl completionSeal transport replay
        provenance localName bundle pkg →
      Cont ring norm normLedger →
        Cont normLedger productControl productRead →
          Cont productRead replay exported →
            PkgSig bundle exported pkg →
              UnaryHistory normLedger ∧ UnaryHistory productRead ∧ UnaryHistory exported ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier normRoute productRoute exportRoute exportedPkg
  obtain ⟨ringUnary, normUnary, _banachUnary, productUnary, _completionUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localNameUnary, _ringNormRoute,
      _completionRoute, _replayRoute, provenancePkg⟩ := carrier
  have normLedgerUnary : UnaryHistory normLedger :=
    unary_cont_closed ringUnary normUnary normRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed normLedgerUnary productUnary productRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed productReadUnary replayUnary exportRoute
  exact
    ⟨normLedgerUnary, productReadUnary, exportedUnary, provenancePkg, exportedPkg⟩

end BEDC.Derived.BanachAlgebraUp
