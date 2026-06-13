import BEDC.Derived.CoveringdimensionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootRefinementOrderRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName refinementRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement refinementRead →
        Cont refinementRead orderBound rootRead →
          PkgSig bundle rootRead pkg →
            UnaryHistory compactMetric ∧ UnaryHistory cover ∧ UnaryHistory refinement ∧
              UnaryHistory orderBound ∧ UnaryHistory lebesgue ∧ UnaryHistory refinementRead ∧
                UnaryHistory rootRead ∧ Cont compactMetric epsilonNet cover ∧
                  Cont cover refinement orderBound ∧ Cont cover refinement refinementRead ∧
                    Cont refinementRead orderBound rootRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverRefinementRead refinementReadOrderRoot rootReadPkg
  obtain ⟨compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverUnary refinementUnary coverRefinementRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed refinementReadUnary orderUnary refinementReadOrderRoot
  exact
    ⟨compactUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
      refinementReadUnary, rootReadUnary, compactEpsilonCover, coverRefinementOrder,
      coverRefinementRead, refinementReadOrderRoot, provenancePkg, rootReadPkg⟩

theorem CoveringDimensionCoverOrderDirectedness [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName leftRefinement rightRefinement commonRefinement : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement leftRefinement →
        Cont cover refinement rightRefinement →
          Cont leftRefinement rightRefinement commonRefinement →
            PkgSig bundle commonRefinement pkg →
              UnaryHistory cover ∧ UnaryHistory refinement ∧ UnaryHistory leftRefinement ∧
                UnaryHistory rightRefinement ∧ UnaryHistory commonRefinement ∧
                  Cont cover refinement leftRefinement ∧
                    Cont cover refinement rightRefinement ∧
                      Cont leftRefinement rightRefinement commonRefinement ∧
                        PkgSig bundle commonRefinement pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverRefinementLeft coverRefinementRight leftRightCommon commonPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have leftUnary : UnaryHistory leftRefinement :=
    unary_cont_closed coverUnary refinementUnary coverRefinementLeft
  have rightUnary : UnaryHistory rightRefinement :=
    unary_cont_closed coverUnary refinementUnary coverRefinementRight
  have commonUnary : UnaryHistory commonRefinement :=
    unary_cont_closed leftUnary rightUnary leftRightCommon
  exact
    ⟨coverUnary, refinementUnary, leftUnary, rightUnary, commonUnary, coverRefinementLeft,
      coverRefinementRight, leftRightCommon, commonPkg⟩

theorem CoveringDimensionCarrier_root_separability_route [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName separabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound separabilityRead →
        PkgSig bundle separabilityRead pkg →
          UnaryHistory cover ∧ UnaryHistory orderBound ∧ UnaryHistory separabilityRead ∧
            Cont compactMetric epsilonNet cover ∧ Cont cover refinement orderBound ∧
              Cont cover orderBound separabilityRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle separabilityRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverOrderSeparability separabilityPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have separabilityUnary : UnaryHistory separabilityRead :=
    unary_cont_closed coverUnary orderUnary coverOrderSeparability
  exact
    ⟨coverUnary, orderUnary, separabilityUnary, compactEpsilonCover, coverRefinementOrder,
      coverOrderSeparability, provenancePkg, separabilityPkg⟩

theorem CoveringDimensionCarrier_root_completion_handoff [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont lebesgue replay completionRead →
        PkgSig bundle completionRead pkg →
          UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
            UnaryHistory refinement ∧ UnaryHistory orderBound ∧ UnaryHistory lebesgue ∧
              UnaryHistory completionRead ∧ Cont compactMetric epsilonNet cover ∧
                Cont cover refinement orderBound ∧ Cont orderBound lebesgue replay ∧
                  Cont lebesgue replay completionRead ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier lebesgueReplayCompletion completionPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localNameUnary, compactEpsilonCover,
    coverRefinementOrder, orderLebesgueReplay, _transportReplayProvenance, _provenancePkg,
    _localNamePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed lebesgueUnary replayUnary lebesgueReplayCompletion
  exact
    ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
      completionUnary, compactEpsilonCover, coverRefinementOrder, orderLebesgueReplay,
      lebesgueReplayCompletion, completionPkg⟩

theorem CoveringDimensionFiniteCoverOrderRefinement [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead realSealRead nerveRead orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement metricRead →
        Cont metricRead orderBound realSealRead →
          Cont realSealRead lebesgue nerveRead →
            Cont nerveRead orderBound orderRead →
              PkgSig bundle orderRead pkg →
                UnaryHistory cover ∧ UnaryHistory refinement ∧ UnaryHistory orderBound ∧
                  UnaryHistory metricRead ∧ UnaryHistory realSealRead ∧
                    UnaryHistory nerveRead ∧ UnaryHistory orderRead ∧
                      Cont cover refinement metricRead ∧
                        Cont metricRead orderBound realSealRead ∧
                          Cont realSealRead lebesgue nerveRead ∧
                            Cont nerveRead orderBound orderRead ∧
                              PkgSig bundle orderRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverRefinementMetric metricOrderRealSeal realSealLebesgueNerve
    nerveOrderRead orderReadPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed coverUnary refinementUnary coverRefinementMetric
  have realSealReadUnary : UnaryHistory realSealRead :=
    unary_cont_closed metricReadUnary orderUnary metricOrderRealSeal
  have nerveReadUnary : UnaryHistory nerveRead :=
    unary_cont_closed realSealReadUnary lebesgueUnary realSealLebesgueNerve
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed nerveReadUnary orderUnary nerveOrderRead
  exact
    ⟨coverUnary, refinementUnary, orderUnary, metricReadUnary, realSealReadUnary,
      nerveReadUnary, orderReadUnary, coverRefinementMetric, metricOrderRealSeal,
      realSealLebesgueNerve, nerveOrderRead, orderReadPkg⟩

theorem CoveringDimensionRealSeparabilityFiniteCoverBudget [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName separabilityBudget coverBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound separabilityBudget →
        Cont separabilityBudget refinement coverBudget →
          PkgSig bundle coverBudget pkg →
            SemanticNameCert
                (fun row : BHist => hsame row coverBudget ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                    hsame row refinement ∨ hsame row orderBound ∨
                      hsame row separabilityBudget ∨ hsame row coverBudget)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont cover orderBound separabilityBudget ∧
                    Cont separabilityBudget refinement coverBudget ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle coverBudget pkg)
                hsame ∧
              UnaryHistory separabilityBudget ∧ UnaryHistory coverBudget := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverOrderSeparability separabilityRefinementCover coverBudgetPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have separabilityUnary : UnaryHistory separabilityBudget :=
    unary_cont_closed coverUnary orderUnary coverOrderSeparability
  have coverBudgetUnary : UnaryHistory coverBudget :=
    unary_cont_closed separabilityUnary refinementUnary separabilityRefinementCover
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverBudget ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row separabilityBudget ∨
                hsame row coverBudget)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cover orderBound separabilityBudget ∧
              Cont separabilityBudget refinement coverBudget ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle coverBudget pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro coverBudget ⟨hsame_refl coverBudget, coverBudgetUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverOrderSeparability, separabilityRefinementCover,
          provenancePkg, coverBudgetPkg⟩
  }
  exact ⟨cert, separabilityUnary, coverBudgetUnary⟩

theorem CoveringDimensionCoverRefinementMonotonicity [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName leftRefinement rightRefinement commonRefinement ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement leftRefinement →
        Cont cover refinement rightRefinement →
          Cont leftRefinement rightRefinement commonRefinement →
            Cont commonRefinement orderBound ledgerRead →
              PkgSig bundle ledgerRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                        hsame row leftRefinement ∨ hsame row rightRefinement ∨
                          hsame row commonRefinement ∨ hsame row ledgerRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont cover refinement leftRefinement ∧
                        Cont cover refinement rightRefinement ∧
                          Cont leftRefinement rightRefinement commonRefinement ∧
                            Cont commonRefinement orderBound ledgerRead ∧
                              PkgSig bundle ledgerRead pkg)
                    hsame ∧
                  UnaryHistory leftRefinement ∧ UnaryHistory rightRefinement ∧
                    UnaryHistory commonRefinement ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverRefinementLeft coverRefinementRight leftRightCommon commonOrderLedger
    ledgerPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have leftUnary : UnaryHistory leftRefinement :=
    unary_cont_closed coverUnary refinementUnary coverRefinementLeft
  have rightUnary : UnaryHistory rightRefinement :=
    unary_cont_closed coverUnary refinementUnary coverRefinementRight
  have commonUnary : UnaryHistory commonRefinement :=
    unary_cont_closed leftUnary rightUnary leftRightCommon
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed commonUnary orderUnary commonOrderLedger
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
              hsame row leftRefinement ∨ hsame row rightRefinement ∨
                hsame row commonRefinement ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cover refinement leftRefinement ∧
              Cont cover refinement rightRefinement ∧
                Cont leftRefinement rightRefinement commonRefinement ∧
                  Cont commonRefinement orderBound ledgerRead ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRefinementLeft, coverRefinementRight, leftRightCommon,
          commonOrderLedger, ledgerPkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary, commonUnary, ledgerUnary⟩

theorem CoveringDimensionRealSeparabilityRefinementRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName completionRead densityRead regseqRead realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont lebesgue transport completionRead →
        Cont completionRead provenance densityRead →
          Cont densityRead replay regseqRead →
            Cont regseqRead localName realSealRead →
              PkgSig bundle realSealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row cover ∨ hsame row refinement ∨
                        hsame row lebesgue ∨ hsame row completionRead ∨
                          hsame row densityRead ∨ hsame row regseqRead ∨
                            hsame row realSealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont lebesgue transport completionRead ∧
                        Cont completionRead provenance densityRead ∧
                          Cont densityRead replay regseqRead ∧
                            Cont regseqRead localName realSealRead ∧
                              PkgSig bundle realSealRead pkg)
                    hsame ∧
                  UnaryHistory completionRead ∧ UnaryHistory densityRead ∧
                    UnaryHistory regseqRead ∧ UnaryHistory realSealRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier lebesgueTransportCompletion completionProvenanceDensity densityReplayRegseq
    regseqLocalRealSeal realSealPkg
  obtain ⟨compactUnary, _epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    lebesgueUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed lebesgueUnary transportUnary lebesgueTransportCompletion
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed completionUnary provenanceUnary completionProvenanceDensity
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed densityUnary replayUnary densityReplayRegseq
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed regseqUnary localNameUnary regseqLocalRealSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row cover ∨ hsame row refinement ∨
              hsame row lebesgue ∨ hsame row completionRead ∨ hsame row densityRead ∨
                hsame row regseqRead ∨ hsame row realSealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lebesgue transport completionRead ∧
              Cont completionRead provenance densityRead ∧ Cont densityRead replay regseqRead ∧
                Cont regseqRead localName realSealRead ∧ PkgSig bundle realSealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realSealRead ⟨hsame_refl realSealRead, realSealUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lebesgueTransportCompletion, completionProvenanceDensity,
          densityReplayRegseq, regseqLocalRealSeal, realSealPkg⟩
  }
  exact ⟨cert, completionUnary, densityUnary, regseqUnary, realSealUnary⟩

theorem CoveringDimensionCompactNetOrderRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactRead supportRead radiusRead completionRead densityRead orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet compactRead →
        Cont compactRead cover supportRead →
          Cont supportRead refinement radiusRead →
            Cont radiusRead lebesgue completionRead →
              Cont completionRead transport densityRead →
                Cont densityRead orderBound orderRead →
                  PkgSig bundle orderRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row compactMetric ∨ hsame row epsilonNet ∨
                            hsame row cover ∨ hsame row refinement ∨
                              hsame row lebesgue ∨ hsame row transport ∨
                                hsame row densityRead ∨ hsame row orderRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont compactMetric epsilonNet compactRead ∧
                            Cont compactRead cover supportRead ∧
                              Cont supportRead refinement radiusRead ∧
                                Cont radiusRead lebesgue completionRead ∧
                                  Cont completionRead transport densityRead ∧
                                    Cont densityRead orderBound orderRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle orderRead pkg)
                        hsame ∧
                      UnaryHistory compactRead ∧ UnaryHistory supportRead ∧
                        UnaryHistory radiusRead ∧ UnaryHistory completionRead ∧
                          UnaryHistory densityRead ∧ UnaryHistory orderRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactEpsilonRead compactReadCover supportRefinement radiusLebesgue
    completionTransport densityOrder orderReadPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed compactUnary epsilonUnary compactEpsilonRead
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed compactReadUnary coverUnary compactReadCover
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed supportReadUnary refinementUnary supportRefinement
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed radiusReadUnary lebesgueUnary radiusLebesgue
  have densityReadUnary : UnaryHistory densityRead :=
    unary_cont_closed completionReadUnary transportUnary completionTransport
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed densityReadUnary orderUnary densityOrder
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row lebesgue ∨ hsame row transport ∨
                hsame row densityRead ∨ hsame row orderRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet compactRead ∧
              Cont compactRead cover supportRead ∧
                Cont supportRead refinement radiusRead ∧
                  Cont radiusRead lebesgue completionRead ∧
                    Cont completionRead transport densityRead ∧
                      Cont densityRead orderBound orderRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle orderRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro orderRead ⟨hsame_refl orderRead, orderReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactEpsilonRead, compactReadCover, supportRefinement,
          radiusLebesgue, completionTransport, densityOrder, provenancePkg, orderReadPkg⟩
  }
  exact
    ⟨cert, compactReadUnary, supportReadUnary, radiusReadUnary, completionReadUnary,
      densityReadUnary, orderReadUnary⟩

theorem CoveringDimensionRootCoverScopeRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactRead supportRead radiusRead orderRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet compactRead →
        Cont compactRead cover supportRead →
          Cont supportRead refinement radiusRead →
            Cont radiusRead orderBound orderRead →
              Cont orderRead replay consumer →
                PkgSig bundle orderRead pkg →
                  PkgSig bundle consumer pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row compactMetric ∨ hsame row epsilonNet ∨
                            hsame row cover ∨ hsame row refinement ∨
                              hsame row orderBound ∨ hsame row orderRead ∨
                                hsame row consumer)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont compactMetric epsilonNet compactRead ∧
                            Cont compactRead cover supportRead ∧
                              Cont supportRead refinement radiusRead ∧
                                Cont radiusRead orderBound orderRead ∧
                                  Cont orderRead replay consumer ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle consumer pkg)
                        hsame := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactEpsilonRead compactReadCover supportRefinement radiusOrder
    orderReplay orderReadPkg consumerPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed compactUnary epsilonUnary compactEpsilonRead
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed compactReadUnary coverUnary compactReadCover
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed supportReadUnary refinementUnary supportRefinement
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed radiusReadUnary orderUnary radiusOrder
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed orderReadUnary replayUnary orderReplay
  exact {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactEpsilonRead, compactReadCover, supportRefinement,
          radiusOrder, orderReplay, provenancePkg, consumerPkg⟩
  }

end BEDC.Derived.CoveringdimensionUp
