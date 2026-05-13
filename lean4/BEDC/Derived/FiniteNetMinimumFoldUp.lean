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

end BEDC.Derived.FiniteNetMinimumFoldUp
