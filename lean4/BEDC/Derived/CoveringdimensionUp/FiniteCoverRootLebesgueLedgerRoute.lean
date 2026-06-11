import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverRootLebesgueLedgerRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName orderRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement orderRead →
        Cont orderRead lebesgue ledgerRead →
          PkgSig bundle ledgerRead pkg →
            UnaryHistory cover ∧ UnaryHistory refinement ∧ UnaryHistory orderBound ∧
              UnaryHistory lebesgue ∧ UnaryHistory orderRead ∧ UnaryHistory ledgerRead ∧
                Cont cover refinement orderRead ∧ Cont orderRead lebesgue ledgerRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverRefinementRead readLebesgueLedger ledgerPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed coverUnary refinementUnary coverRefinementRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed orderReadUnary lebesgueUnary readLebesgueLedger
  exact
    ⟨coverUnary, refinementUnary, orderUnary, lebesgueUnary, orderReadUnary,
      ledgerReadUnary, coverRefinementRead, readLebesgueLedger, provenancePkg, ledgerPkg⟩

end BEDC.Derived.CoveringdimensionUp
