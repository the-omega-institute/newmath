import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DoCalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DoCalculusPacket [AskSetup] [PackageSetup]
    (intervention variables adjustment distribution independence expectation «export» htrans replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory intervention ∧ UnaryHistory variables ∧ UnaryHistory adjustment ∧
    UnaryHistory distribution ∧ UnaryHistory independence ∧ UnaryHistory expectation ∧
      UnaryHistory «export» ∧ UnaryHistory htrans ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont intervention variables adjustment ∧ Cont adjustment distribution independence ∧
            Cont independence expectation «export» ∧ Cont htrans replay provenance ∧
              PkgSig bundle localName pkg

theorem DoCalculusPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {intervention variables adjustment distribution independence expectation «export» htrans replay
      provenance localName interventionRead adjustmentRead probabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DoCalculusPacket intervention variables adjustment distribution independence expectation «export»
        htrans replay provenance localName bundle pkg →
      Cont intervention variables interventionRead →
        Cont adjustment independence adjustmentRead →
          Cont expectation «export» probabilityRead →
            PkgSig bundle localName pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row localName ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row interventionRead ∨ hsame row adjustmentRead ∨
                      hsame row probabilityRead ∨ hsame row localName)
                  (fun row : BHist => PkgSig bundle localName pkg ∧ hsame row localName)
                  hsame ∧
                UnaryHistory interventionRead ∧ UnaryHistory adjustmentRead ∧
                  UnaryHistory probabilityRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg
  intro packet interventionCont adjustmentCont probabilityCont localNamePkg
  obtain ⟨interventionUnary, variablesUnary, adjustmentUnary, _distributionUnary,
    independenceUnary, expectationUnary, exportUnary, _htransUnary, _replayUnary,
    _provenanceUnary, localNameUnary, _interventionVariablesAdjustment,
    _adjustmentDistributionIndependence, _independenceExpectationExport,
    _htransReplayProvenance, _packetNamePkg⟩ := packet
  have interventionReadUnary : UnaryHistory interventionRead :=
    unary_cont_closed interventionUnary variablesUnary interventionCont
  have adjustmentReadUnary : UnaryHistory adjustmentRead :=
    unary_cont_closed adjustmentUnary independenceUnary adjustmentCont
  have probabilityReadUnary : UnaryHistory probabilityRead :=
    unary_cont_closed expectationUnary exportUnary probabilityCont
  have sourceAtLocalName : hsame localName localName ∧ UnaryHistory localName :=
    ⟨hsame_refl localName, localNameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row interventionRead ∨ hsame row adjustmentRead ∨
              hsame row probabilityRead ∨ hsame row localName)
          (fun row : BHist => PkgSig bundle localName pkg ∧ hsame row localName)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceAtLocalName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨localNamePkg, source.left⟩
  }
  exact ⟨cert, interventionReadUnary, adjustmentReadUnary, probabilityReadUnary⟩

theorem DoCalculusPacket_adjustment_ledger_exactness [AskSetup] [PackageSetup]
    {intervention variables adjustment distribution independence expectation exported htrans replay
      provenance localName adjustmentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DoCalculusPacket intervention variables adjustment distribution independence expectation exported
        htrans replay provenance localName bundle pkg ->
      Cont adjustment independence adjustmentRead ->
        PkgSig bundle adjustmentRead pkg ->
          UnaryHistory variables ∧ UnaryHistory adjustment ∧ UnaryHistory independence ∧
            UnaryHistory adjustmentRead ∧ Cont intervention variables adjustment ∧
              Cont adjustment distribution independence ∧
                Cont adjustment independence adjustmentRead ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle adjustmentRead pkg := by
  intro packet adjustmentRow adjustmentPkg
  obtain ⟨_interventionUnary, variablesUnary, adjustmentUnary, _distributionUnary,
    independenceUnary, _expectationUnary, _exportedUnary, _htransUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, interventionVariablesAdjustment,
    adjustmentDistributionIndependence, _independenceExpectationExport,
    _htransReplayProvenance, localNamePkg⟩ := packet
  have adjustmentReadUnary : UnaryHistory adjustmentRead :=
    unary_cont_closed adjustmentUnary independenceUnary adjustmentRow
  exact
    ⟨variablesUnary, adjustmentUnary, independenceUnary, adjustmentReadUnary,
      interventionVariablesAdjustment, adjustmentDistributionIndependence, adjustmentRow,
      localNamePkg, adjustmentPkg⟩

theorem DoCalculusPacket_intervention_non_escape [AskSetup] [PackageSetup]
    {intervention variables adjustment distribution independence expectation exported htrans replay
      provenance localName interventionRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DoCalculusPacket intervention variables adjustment distribution independence expectation exported
        htrans replay provenance localName bundle pkg ->
      Cont intervention variables interventionRead ->
        hsame localRead localName ->
          PkgSig bundle localName pkg ->
            UnaryHistory interventionRead ∧ UnaryHistory localRead ∧
              Cont intervention variables interventionRead ∧ PkgSig bundle localName pkg ∧
                hsame localRead localName := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory ProbeBundle Pkg
  intro packet interventionRoute localReadSame localNamePkg
  obtain ⟨interventionUnary, variablesUnary, _adjustmentUnary, _distributionUnary,
    _independenceUnary, _expectationUnary, _exportedUnary, _htransUnary, _replayUnary,
    _provenanceUnary, localNameUnary, _interventionVariablesAdjustment,
    _adjustmentDistributionIndependence, _independenceExpectationExport,
    _htransReplayProvenance, _packetNamePkg⟩ := packet
  have interventionReadUnary : UnaryHistory interventionRead :=
    unary_cont_closed interventionUnary variablesUnary interventionRoute
  have localReadUnary : UnaryHistory localRead :=
    unary_transport_symm localNameUnary localReadSame
  exact
    ⟨interventionReadUnary, localReadUnary, interventionRoute, localNamePkg,
      localReadSame⟩

end BEDC.Derived.DoCalculusUp
