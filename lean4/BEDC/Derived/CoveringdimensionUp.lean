import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringDimensionCarrier [AskSetup] [PackageSetup]
    (compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
    UnaryHistory refinement ∧ UnaryHistory orderBound ∧ UnaryHistory lebesgue ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont compactMetric epsilonNet cover ∧
          Cont cover refinement orderBound ∧ Cont orderBound lebesgue replay ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem CoveringDimensionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound
              lebesgue transport replay provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound
              lebesgue transport replay provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier
  have carrierSource := carrier
  obtain ⟨_compactUnary, _epsilonUnary, _coverUnary, _refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨carrierSource, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport localNameUnary (hsame_symm source.right), localNamePkg⟩
  }

theorem CoveringDimensionCarrier_compact_net_admission [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist => PkgSig bundle provenance pkg ∨ PkgSig bundle localName pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro compactMetric (Or.inl (hsame_refl compactMetric))
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
        cases source with
        | inl compactSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) compactSource)
        | inr rest =>
            cases rest with
            | inl epsilonSource =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) epsilonSource))
            | inr coverSource =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) coverSource))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl compactSource =>
          exact unary_transport compactUnary (hsame_symm compactSource)
      | inr rest =>
          cases rest with
          | inl epsilonSource =>
              exact unary_transport epsilonUnary (hsame_symm epsilonSource)
          | inr coverSource =>
              exact unary_transport coverUnary (hsame_symm coverSource)
    ledger_sound := by
      intro _row _source
      exact Or.inl provenancePkg
  }

theorem CoveringDimensionFiniteEpsilonNetCarrier [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName sample : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover sample →
        PkgSig bundle sample pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row epsilonNet ∨ hsame row cover ∨ hsame row refinement ∨
                  hsame row orderBound ∨ hsame row sample)
              (fun row : BHist => UnaryHistory row)
              (fun row : BHist => PkgSig bundle localName pkg ∨ PkgSig bundle sample pkg)
              hsame ∧
            UnaryHistory sample := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier epsilonCoverSample samplePkg
  obtain ⟨_compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have sampleUnary : UnaryHistory sample :=
    unary_cont_closed epsilonUnary coverUnary epsilonCoverSample
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro epsilonNet (Or.inl (hsame_refl epsilonNet))
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
          intro row other sameRows source
          cases source with
          | inl epsilonSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) epsilonSource)
          | inr rest =>
              cases rest with
              | inl coverSource =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) coverSource))
              | inr rest =>
                  cases rest with
                  | inl refinementSource =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) refinementSource)))
                  | inr rest =>
                      cases rest with
                      | inl orderSource =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm sameRows) orderSource))))
                      | inr sampleSource =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr (hsame_trans (hsame_symm sameRows) sampleSource))))
      }
      pattern_sound := by
        intro row source
        cases source with
        | inl epsilonSource =>
            exact unary_transport epsilonUnary (hsame_symm epsilonSource)
        | inr rest =>
            cases rest with
            | inl coverSource =>
                exact unary_transport coverUnary (hsame_symm coverSource)
            | inr rest =>
                cases rest with
                | inl refinementSource =>
                    exact unary_transport refinementUnary (hsame_symm refinementSource)
                | inr rest =>
                    cases rest with
                    | inl orderSource =>
                        exact unary_transport orderUnary (hsame_symm orderSource)
                    | inr sampleSource =>
                        exact unary_transport sampleUnary (hsame_symm sampleSource)
      ledger_sound := by
        intro row source
        cases source with
        | inl _epsilonSource =>
            exact Or.inl localNamePkg
        | inr rest =>
            cases rest with
            | inl _coverSource =>
                exact Or.inl localNamePkg
            | inr rest =>
                cases rest with
                | inl _refinementSource =>
                    exact Or.inl localNamePkg
                | inr rest =>
                    cases rest with
                    | inl _orderSource =>
                        exact Or.inl localNamePkg
                    | inr _sampleSource =>
                        exact Or.inr samplePkg
    }
  · exact sampleUnary

theorem CoveringDimensionCarrier_finite_cover_admission [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover coverRead →
        PkgSig bundle coverRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row cover ∨ hsame row coverRead ∨ hsame row refinement ∨
                  hsame row orderBound)
              (fun row : BHist => UnaryHistory row)
              (fun _row : BHist => PkgSig bundle coverRead pkg ∨ PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory coverRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier epsilonCoverRead coverReadPkg
  obtain ⟨_compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed epsilonUnary coverUnary epsilonCoverRead
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro cover (Or.inl (hsame_refl cover))
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
          cases source with
          | inl coverSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) coverSource)
          | inr rest =>
              cases rest with
              | inl coverReadSource =>
                  exact
                    Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) coverReadSource))
              | inr rest =>
                  cases rest with
                  | inl refinementSource =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) refinementSource)))
                  | inr orderSource =>
                      exact
                        Or.inr
                          (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) orderSource)))
      }
      pattern_sound := by
        intro _row source
        cases source with
        | inl coverSource =>
            exact unary_transport coverUnary (hsame_symm coverSource)
        | inr rest =>
            cases rest with
            | inl coverReadSource =>
                exact unary_transport coverReadUnary (hsame_symm coverReadSource)
            | inr rest =>
                cases rest with
                | inl refinementSource =>
                    exact unary_transport refinementUnary (hsame_symm refinementSource)
                | inr orderSource =>
                    exact unary_transport orderUnary (hsame_symm orderSource)
      ledger_sound := by
        intro _row source
        cases source with
        | inl _coverSource =>
            exact Or.inr localNamePkg
        | inr rest =>
            cases rest with
            | inl _coverReadSource =>
                exact Or.inl coverReadPkg
            | inr rest =>
                cases rest with
                | inl _refinementSource =>
                    exact Or.inr localNamePkg
                | inr _orderSource =>
                    exact Or.inr localNamePkg
    }
  · exact coverReadUnary

theorem CoveringDimensionFiniteCoverRootBoundary [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName coverRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover coverRead →
        Cont coverRead refinement boundaryRead →
          PkgSig bundle boundaryRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row cover ∨ hsame row coverRead ∨ hsame row refinement ∨
                    hsame row boundaryRead)
                (fun row : BHist => UnaryHistory row)
                (fun _row : BHist => PkgSig bundle boundaryRead pkg ∨
                  PkgSig bundle localName pkg)
                hsame ∧
              UnaryHistory coverRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier epsilonCoverRead coverReadRefinementBoundary boundaryReadPkg
  obtain ⟨_compactUnary, epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed epsilonUnary coverUnary epsilonCoverRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed coverReadUnary refinementUnary coverReadRefinementBoundary
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro cover (Or.inl (hsame_refl cover))
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
          cases source with
          | inl coverSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) coverSource)
          | inr rest =>
              cases rest with
              | inl coverReadSource =>
                  exact
                    Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) coverReadSource))
              | inr rest =>
                  cases rest with
                  | inl refinementSource =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) refinementSource)))
                  | inr boundaryReadSource =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (hsame_trans (hsame_symm sameRows) boundaryReadSource)))
      }
      pattern_sound := by
        intro _row source
        cases source with
        | inl coverSource =>
            exact unary_transport coverUnary (hsame_symm coverSource)
        | inr rest =>
            cases rest with
            | inl coverReadSource =>
                exact unary_transport coverReadUnary (hsame_symm coverReadSource)
            | inr rest =>
                cases rest with
                | inl refinementSource =>
                    exact unary_transport refinementUnary (hsame_symm refinementSource)
                | inr boundaryReadSource =>
                    exact unary_transport boundaryReadUnary (hsame_symm boundaryReadSource)
      ledger_sound := by
        intro _row source
        cases source with
        | inl _coverSource =>
            exact Or.inr localNamePkg
        | inr rest =>
            cases rest with
            | inl _coverReadSource =>
                exact Or.inr localNamePkg
            | inr rest =>
                cases rest with
                | inl _refinementSource =>
                    exact Or.inr localNamePkg
                | inr _boundaryReadSource =>
                    exact Or.inl boundaryReadPkg
    }
  · exact ⟨coverReadUnary, boundaryReadUnary⟩

theorem CoveringDimensionRefinementOrderRootUnblock [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName refinementRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement refinementRead →
        Cont refinementRead orderBound rootRead →
          PkgSig bundle rootRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row refinement ∨ hsame row refinementRead ∨
                    hsame row orderBound ∨ hsame row rootRead)
                (fun row : BHist => UnaryHistory row)
                (fun _row : BHist => PkgSig bundle rootRead pkg ∨
                  PkgSig bundle localName pkg)
                hsame ∧
              UnaryHistory refinementRead ∧ UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier coverRefinementRead refinementReadOrderRoot rootReadPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverUnary refinementUnary coverRefinementRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed refinementReadUnary orderUnary refinementReadOrderRoot
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro refinement (Or.inl (hsame_refl refinement))
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
          cases source with
          | inl refinementSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) refinementSource)
          | inr rest =>
              cases rest with
              | inl refinementReadSource =>
                  exact
                    Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) refinementReadSource))
              | inr rest =>
                  cases rest with
                  | inl orderBoundSource =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) orderBoundSource)))
                  | inr rootReadSource =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) rootReadSource)))
      }
      pattern_sound := by
        intro _row source
        cases source with
        | inl refinementSource =>
            exact unary_transport refinementUnary (hsame_symm refinementSource)
        | inr rest =>
            cases rest with
            | inl refinementReadSource =>
                exact unary_transport refinementReadUnary (hsame_symm refinementReadSource)
            | inr rest =>
                cases rest with
                | inl orderBoundSource =>
                    exact unary_transport orderUnary (hsame_symm orderBoundSource)
                | inr rootReadSource =>
                    exact unary_transport rootReadUnary (hsame_symm rootReadSource)
      ledger_sound := by
        intro _row source
        cases source with
        | inl _refinementSource =>
            exact Or.inr localNamePkg
        | inr rest =>
            cases rest with
            | inl _refinementReadSource =>
                exact Or.inr localNamePkg
            | inr rest =>
                cases rest with
                | inl _orderBoundSource =>
                    exact Or.inr localNamePkg
                | inr _rootReadSource =>
                    exact Or.inl rootReadPkg
    }
  · exact ⟨refinementReadUnary, rootReadUnary⟩

theorem CoveringDimensionFiniteCoverRootStability [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName rootRead stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound rootRead →
        Cont rootRead lebesgue stableRead →
          PkgSig bundle stableRead pkg →
            UnaryHistory compactMetric ∧ UnaryHistory cover ∧ UnaryHistory orderBound ∧
              UnaryHistory lebesgue ∧ UnaryHistory rootRead ∧ UnaryHistory stableRead ∧
                Cont compactMetric epsilonNet cover ∧ Cont cover refinement orderBound ∧
                  Cont cover orderBound rootRead ∧ Cont rootRead lebesgue stableRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle stableRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverOrderRoot rootLebesgueStable stablePkg
  obtain ⟨compactUnary, _epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    compactEpsilonCover, coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed coverUnary orderUnary coverOrderRoot
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed rootUnary lebesgueUnary rootLebesgueStable
  exact
    ⟨compactUnary, coverUnary, orderUnary, lebesgueUnary, rootUnary, stableUnary,
      compactEpsilonCover, coverRefinementOrder, coverOrderRoot, rootLebesgueStable,
      provenancePkg, stablePkg⟩

theorem CoveringDimensionLedgerNonEscape [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont replay localName consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
            UnaryHistory refinement ∧ UnaryHistory orderBound ∧ UnaryHistory lebesgue ∧
              UnaryHistory replay ∧ UnaryHistory localName ∧ UnaryHistory consumer ∧
                Cont compactMetric epsilonNet cover ∧ Cont cover refinement orderBound ∧
                  Cont orderBound lebesgue replay ∧ Cont replay localName consumer ∧
                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier replayLocalNameConsumer consumerPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, replayUnary, _provenanceUnary, localNameUnary,
    compactEpsilonCover, coverRefinementOrder, orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed replayUnary localNameUnary replayLocalNameConsumer
  exact
    ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
      replayUnary, localNameUnary, consumerUnary, compactEpsilonCover, coverRefinementOrder,
      orderLebesgueReplay, replayLocalNameConsumer, consumerPkg⟩

theorem CoveringDimensionCompactNetOrderAdmission [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactRead supportRead radiusRead orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet compactRead →
        Cont compactRead cover supportRead →
          Cont supportRead refinement radiusRead →
            Cont radiusRead orderBound orderRead →
              PkgSig bundle orderRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                        hsame row refinement ∨ hsame row orderBound ∨ hsame row orderRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont compactMetric epsilonNet compactRead ∧
                        Cont compactRead cover supportRead ∧
                          Cont supportRead refinement radiusRead ∧
                            Cont radiusRead orderBound orderRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle orderRead pkg)
                    hsame ∧
                  UnaryHistory compactRead ∧ UnaryHistory supportRead ∧
                    UnaryHistory radiusRead ∧ UnaryHistory orderRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier compactRoute supportRoute radiusRoute orderRoute orderPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed compactUnary epsilonUnary compactRoute
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed compactReadUnary coverUnary supportRoute
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed supportReadUnary refinementUnary radiusRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed radiusReadUnary orderUnary orderRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row orderRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet compactRead ∧
              Cont compactRead cover supportRead ∧
                Cont supportRead refinement radiusRead ∧
                  Cont radiusRead orderBound orderRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle orderRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro orderRead ⟨hsame_refl orderRead, orderReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRoute, supportRoute, radiusRoute, orderRoute,
          provenancePkg, orderPkg⟩
  }
  exact ⟨cert, compactReadUnary, supportReadUnary, radiusReadUnary, orderReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
