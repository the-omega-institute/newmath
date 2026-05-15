import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteNetMinimumFoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteNetMinimumFoldPacket [AskSetup] [PackageSetup]
    (bundleRow radius accumulator lower transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundleRow ∧ UnaryHistory radius ∧ UnaryHistory accumulator ∧
    UnaryHistory lower ∧ UnaryHistory nameRow ∧
      Cont bundleRow radius accumulator ∧ Cont accumulator lower transport ∧
        Cont transport nameRow provenance ∧ Cont bundleRow radius transport ∧
          Cont transport accumulator lower ∧ Cont lower route provenance ∧
            PkgSig bundle provenance pkg

theorem FiniteNetMinimumFoldPacket_namecert_obligations [AskSetup] [PackageSetup]
    {probeRow radiusRow accumulator lowerBound transportRow routeRow provenance nameRow exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket probeRow radiusRow accumulator lowerBound transportRow
        routeRow provenance nameRow bundle pkg →
      Cont accumulator lowerBound exported →
        PkgSig bundle exported pkg →
          SemanticNameCert
            (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist => Cont accumulator lowerBound row ∧
              Cont probeRow radiusRow accumulator)
            (fun row : BHist => PkgSig bundle row pkg ∧
              Cont transportRow nameRow provenance)
            (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet exportRoute exportPkg
  obtain ⟨probeUnary, radiusUnary, accumulatorUnary, lowerBoundUnary, _nameRowUnary,
    probeRadiusAccumulator, _accumulatorLowerTransport, transportNameProvenance,
    _probeRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _provenancePkg⟩ := packet
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed accumulatorUnary lowerBoundUnary exportRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨cont_result_hsame_transport exportRoute (hsame_symm sourceRow.left),
          probeRadiusAccumulator⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, transportNameProvenance⟩
  }

theorem FiniteNetMinimumFoldPacket_nonempty_probe_exhaustion [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow consumed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont bundleRow radius consumed →
        Cont consumed accumulator lower →
          PkgSig bundle provenance pkg →
            UnaryHistory bundleRow ∧ UnaryHistory radius ∧ UnaryHistory accumulator ∧
              UnaryHistory consumed ∧ Cont bundleRow radius consumed ∧
                Cont consumed accumulator lower ∧ PkgSig bundle provenance pkg := by
  intro packet bundleRadiusConsumed consumedAccumulatorLower provenancePkg
  obtain ⟨bundleRowUnary, radiusUnary, accumulatorUnary, _lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, _accumulatorLowerTransport, _transportNameProvenance,
    _transportRoute, _lowerRoute, _provenanceRoute, _packetPkg⟩ := packet
  have consumedUnary : UnaryHistory consumed :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusConsumed
  exact
    ⟨bundleRowUnary, radiusUnary, accumulatorUnary, consumedUnary, bundleRadiusConsumed,
      consumedAccumulatorLower, provenancePkg⟩

theorem FiniteNetMinimumFoldPacket_lower_bound_certificate [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow lowerExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont accumulator lower lowerExport →
        PkgSig bundle lowerExport pkg →
          UnaryHistory accumulator ∧ UnaryHistory lower ∧ UnaryHistory lowerExport ∧
            Cont accumulator lower lowerExport ∧ PkgSig bundle lowerExport pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro packet accumulatorLowerExport lowerExportPkg
  obtain ⟨_bundleRowUnary, _radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, _accumulatorLowerTransport, _transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _provenancePkg⟩ := packet
  have lowerExportUnary : UnaryHistory lowerExport :=
    unary_cont_closed accumulatorUnary lowerUnary accumulatorLowerExport
  exact
    ⟨accumulatorUnary, lowerUnary, lowerExportUnary, accumulatorLowerExport, lowerExportPkg⟩

theorem FiniteNetMinimumFoldPacket_radius_ledger_admission [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow admitted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont bundleRow radius admitted →
        PkgSig bundle provenance pkg →
          UnaryHistory bundleRow ∧ UnaryHistory radius ∧ UnaryHistory admitted ∧
            Cont bundleRow radius admitted ∧ Cont bundleRow radius accumulator ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro packet bundleRadiusAdmitted provenancePkg
  obtain ⟨bundleRowUnary, radiusUnary, _accumulatorUnary, _lowerUnary, _nameRowUnary,
    bundleRadiusAccumulator, _accumulatorLowerTransport, _transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _packetPkg⟩ := packet
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusAdmitted
  exact
    ⟨bundleRowUnary, radiusUnary, admittedUnary, bundleRadiusAdmitted,
      bundleRadiusAccumulator, provenancePkg⟩

theorem FiniteNetMinimumFoldPacket_compactmoduluscover_input_exactness
    [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow compactInput folded
      exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont bundleRow radius compactInput →
        Cont compactInput accumulator folded →
          Cont folded lower exported →
            PkgSig bundle exported pkg →
              UnaryHistory bundleRow ∧ UnaryHistory radius ∧ UnaryHistory accumulator ∧
                UnaryHistory lower ∧ UnaryHistory compactInput ∧ UnaryHistory folded ∧
                  UnaryHistory exported ∧ Cont bundleRow radius compactInput ∧
                    Cont compactInput accumulator folded ∧ Cont folded lower exported ∧
                      Cont transport nameRow provenance ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle exported pkg := by
  intro packet bundleRadiusCompact compactAccumulatorFolded foldedLowerExported exportedPkg
  obtain ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, _accumulatorLowerTransport, transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    provenancePkg⟩ := packet
  have compactInputUnary : UnaryHistory compactInput :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusCompact
  have foldedUnary : UnaryHistory folded :=
    unary_cont_closed compactInputUnary accumulatorUnary compactAccumulatorFolded
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed foldedUnary lowerUnary foldedLowerExported
  exact
    ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, compactInputUnary, foldedUnary,
      exportedUnary, bundleRadiusCompact, compactAccumulatorFolded, foldedLowerExported,
      transportNameProvenance, provenancePkg, exportedPkg⟩

theorem FiniteNetMinimumFoldPacket_uniformmodulus_output_exhaustion
    [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow uniformOutput :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      hsame uniformOutput accumulator →
        PkgSig bundle provenance pkg →
          UnaryHistory accumulator ∧ UnaryHistory lower ∧ UnaryHistory uniformOutput ∧
            Cont accumulator lower transport ∧ Cont transport nameRow provenance ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro packet outputSame provenancePkg
  obtain ⟨_bundleRowUnary, _radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, accumulatorLowerTransport, transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _packetPkg⟩ := packet
  have uniformOutputUnary : UnaryHistory uniformOutput :=
    unary_transport_symm accumulatorUnary outputSame
  exact
    ⟨accumulatorUnary, lowerUnary, uniformOutputUnary, accumulatorLowerTransport,
      transportNameProvenance, provenancePkg⟩

theorem FiniteNetMinimumFoldPacket_positive_precision_obligation [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow positivePrecision :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont accumulator lower transport →
        hsame positivePrecision transport →
          PkgSig bundle provenance pkg →
            UnaryHistory accumulator ∧ UnaryHistory lower ∧ UnaryHistory transport ∧
              UnaryHistory positivePrecision ∧ Cont accumulator lower transport ∧
                hsame positivePrecision transport ∧ PkgSig bundle provenance pkg := by
  intro packet accumulatorLowerTransport positiveSame provenancePkg
  obtain ⟨_bundleRowUnary, _radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, _packetAccumulatorLowerTransport, _transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _packetPkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed accumulatorUnary lowerUnary accumulatorLowerTransport
  have positivePrecisionUnary : UnaryHistory positivePrecision :=
    unary_transport_symm transportUnary positiveSame
  exact
    ⟨accumulatorUnary, lowerUnary, transportUnary, positivePrecisionUnary,
      accumulatorLowerTransport, positiveSame, provenancePkg⟩

theorem FiniteNetMinimumFoldPacket_uniform_modulus_handoff [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont accumulator lower handoff →
        hsame handoff transport →
          PkgSig bundle handoff pkg →
            UnaryHistory accumulator ∧ UnaryHistory lower ∧ UnaryHistory handoff ∧
              Cont accumulator lower handoff ∧ Cont accumulator lower transport ∧
                hsame handoff transport ∧ PkgSig bundle handoff pkg := by
  intro packet accumulatorLowerHandoff handoffSame handoffPkg
  obtain ⟨_bundleRowUnary, _radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, accumulatorLowerTransport, _transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _packetPkg⟩ := packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed accumulatorUnary lowerUnary accumulatorLowerHandoff
  exact
    ⟨accumulatorUnary, lowerUnary, handoffUnary, accumulatorLowerHandoff,
      accumulatorLowerTransport, handoffSame, handoffPkg⟩

theorem FiniteNetMinimumFoldPacket_compactmetric_probe_consumption
    [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow compactInput folded
      lowerExport uniformOutput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont bundleRow radius compactInput →
        Cont compactInput accumulator folded →
          Cont folded lower lowerExport →
            hsame uniformOutput accumulator →
              PkgSig bundle provenance pkg →
                PkgSig bundle lowerExport pkg →
                  UnaryHistory compactInput ∧ UnaryHistory folded ∧
                    UnaryHistory lowerExport ∧ UnaryHistory uniformOutput ∧
                      Cont bundleRow radius compactInput ∧
                        Cont compactInput accumulator folded ∧
                          Cont folded lower lowerExport ∧
                            Cont accumulator lower transport ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle lowerExport pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg hsame
  intro packet bundleRadiusCompact compactAccumulatorFolded foldedLowerExport
    outputSame provenancePkg lowerExportPkg
  obtain ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, accumulatorLowerTransport, _transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _packetPkg⟩ := packet
  have compactInputUnary : UnaryHistory compactInput :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusCompact
  have foldedUnary : UnaryHistory folded :=
    unary_cont_closed compactInputUnary accumulatorUnary compactAccumulatorFolded
  have lowerExportUnary : UnaryHistory lowerExport :=
    unary_cont_closed foldedUnary lowerUnary foldedLowerExport
  have uniformOutputUnary : UnaryHistory uniformOutput :=
    unary_transport_symm accumulatorUnary outputSame
  exact
    ⟨compactInputUnary, foldedUnary, lowerExportUnary, uniformOutputUnary,
      bundleRadiusCompact, compactAccumulatorFolded, foldedLowerExport,
      accumulatorLowerTransport, provenancePkg, lowerExportPkg⟩

theorem FiniteNetMinimumFoldPacket_selector_stability [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow selector selected
      exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg ->
      Cont transport accumulator selector ->
        Cont selector lower selected ->
          Cont selected nameRow exported ->
            PkgSig bundle exported pkg ->
              UnaryHistory transport ∧ UnaryHistory accumulator ∧ UnaryHistory selector ∧
                UnaryHistory selected ∧ UnaryHistory exported ∧
                  Cont transport accumulator selector ∧ Cont selector lower selected ∧
                    Cont selected nameRow exported ∧ PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro packet transportAccumulatorSelector selectorLowerSelected selectedNameExported exportedPkg
  obtain ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, nameRowUnary,
    _bundleRadiusAccumulator, _accumulatorLowerTransport, _transportNameProvenance,
    bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _provenancePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusTransport
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed transportUnary accumulatorUnary transportAccumulatorSelector
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed selectorUnary lowerUnary selectorLowerSelected
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed selectedUnary nameRowUnary selectedNameExported
  exact
    ⟨transportUnary, accumulatorUnary, selectorUnary, selectedUnary, exportedUnary,
      transportAccumulatorSelector, selectorLowerSelected, selectedNameExported, exportedPkg⟩

theorem FiniteNetMinimumFoldPacket_order_selector_transport [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow selector selected
      transported exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg ->
      Cont transport accumulator selector ->
        Cont selector lower selected ->
          hsame transported selected ->
            Cont transported nameRow exported ->
              PkgSig bundle exported pkg ->
                UnaryHistory selector ∧ UnaryHistory selected ∧ UnaryHistory transported ∧
                  UnaryHistory exported ∧ Cont transport accumulator selector ∧
                    Cont selector lower selected ∧ hsame transported selected ∧
                      Cont transported nameRow exported ∧ Cont lower route provenance ∧
                        PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame ProbeBundle Pkg
  intro packet transportAccumulatorSelector selectorLowerSelected transportedSame
    transportedNameExported exportedPkg
  obtain ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, nameRowUnary,
    _bundleRadiusAccumulator, _accumulatorLowerTransport, _transportNameProvenance,
    bundleRadiusTransport, _transportAccumulatorLower, lowerRouteProvenance,
    _provenancePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusTransport
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed transportUnary accumulatorUnary transportAccumulatorSelector
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed selectorUnary lowerUnary selectorLowerSelected
  have transportedUnary : UnaryHistory transported :=
    unary_transport_symm selectedUnary transportedSame
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed transportedUnary nameRowUnary transportedNameExported
  exact
    ⟨selectorUnary, selectedUnary, transportedUnary, exportedUnary,
      transportAccumulatorSelector, selectorLowerSelected, transportedSame,
      transportedNameExported, lowerRouteProvenance, exportedPkg⟩

theorem FiniteNetMinimumFoldPacket_compact_uniform_modulus_consumption
    [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow compactInput folded
      lowerExport handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg ->
      Cont bundleRow radius compactInput ->
        Cont compactInput accumulator folded ->
          Cont folded lower lowerExport ->
            Cont accumulator lower handoff ->
              hsame handoff transport ->
                PkgSig bundle lowerExport pkg ->
                  PkgSig bundle handoff pkg ->
                    UnaryHistory bundleRow ∧ UnaryHistory radius ∧
                      UnaryHistory accumulator ∧ UnaryHistory lower ∧
                        UnaryHistory compactInput ∧ UnaryHistory folded ∧
                          UnaryHistory lowerExport ∧ UnaryHistory handoff ∧
                            Cont bundleRow radius compactInput ∧
                              Cont compactInput accumulator folded ∧
                                Cont folded lower lowerExport ∧
                                  Cont accumulator lower handoff ∧
                                    Cont accumulator lower transport ∧
                                      hsame handoff transport ∧
                                        PkgSig bundle lowerExport pkg ∧
                                          PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame ProbeBundle Pkg
  intro packet bundleRadiusCompact compactAccumulatorFolded foldedLowerExport
    accumulatorLowerHandoff handoffSame lowerExportPkg handoffPkg
  obtain ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, accumulatorLowerTransport, _transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _provenancePkg⟩ := packet
  have compactInputUnary : UnaryHistory compactInput :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusCompact
  have foldedUnary : UnaryHistory folded :=
    unary_cont_closed compactInputUnary accumulatorUnary compactAccumulatorFolded
  have lowerExportUnary : UnaryHistory lowerExport :=
    unary_cont_closed foldedUnary lowerUnary foldedLowerExport
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed accumulatorUnary lowerUnary accumulatorLowerHandoff
  exact
    ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, compactInputUnary,
      foldedUnary, lowerExportUnary, handoffUnary, bundleRadiusCompact,
      compactAccumulatorFolded, foldedLowerExport, accumulatorLowerHandoff,
      accumulatorLowerTransport, handoffSame, lowerExportPkg, handoffPkg⟩

end BEDC.Derived.FiniteNetMinimumFoldUp
