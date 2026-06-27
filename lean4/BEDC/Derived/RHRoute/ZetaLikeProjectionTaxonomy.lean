import BEDC.Derived.OnticCollapseModes
import BEDC.Derived.RHRoute.ConstructiveZeta
import BEDC.Derived.RHRoute.ObjectRealityInductionRoute
import BEDC.Derived.RHRoute.ZetaBoxEvaluator
import BEDC.Derived.RHRoute.ZetaInheritedInvariants
import BEDC.Derived.RHRoute.ZetaZeroLocated
import BEDC.Derived.UnifiedRelationAtlasUp
import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.Derived.ZetaZerosUp

namespace BEDC.Derived.RHRoute.ZetaLikeProjectionTaxonomy

open BEDC.Derived.OnticCollapseModes
open BEDC.Derived.UnifiedRelationAtlasUp
open BEDC.Derived.RHRoute.ObjectRealityInductionRoute

/-!
本文件把已经编码的 zeta-facing 对象按本体投影读法列成有限分类表。
分类只覆盖本仓库已有 Lean 对象, 不声称零点位置或解析闭合。
-/

inductive ZetaProjectionKind where
  | dirichletAtlas
  | etaEvaluation
  | zeroLedger
  | continuationWitness
  | onticGeneratedPacket
  | locatedBoxEvaluation

inductive KnownZetaLikeProjection where
  | atlasDirichlet
  | constructiveEta
  | zeroLedger
  | continuationWitness
  | generatedOntic
  | locatedBox

def zetaProjectionKindCode : ZetaProjectionKind -> Nat
  | ZetaProjectionKind.dirichletAtlas => 0
  | ZetaProjectionKind.etaEvaluation => 1
  | ZetaProjectionKind.zeroLedger => 2
  | ZetaProjectionKind.continuationWitness => 3
  | ZetaProjectionKind.onticGeneratedPacket => 4
  | ZetaProjectionKind.locatedBoxEvaluation => 5

def knownZetaProjectionCode : KnownZetaLikeProjection -> Nat
  | KnownZetaLikeProjection.atlasDirichlet => 0
  | KnownZetaLikeProjection.constructiveEta => 1
  | KnownZetaLikeProjection.zeroLedger => 2
  | KnownZetaLikeProjection.continuationWitness => 3
  | KnownZetaLikeProjection.generatedOntic => 4
  | KnownZetaLikeProjection.locatedBox => 5

def zetaProjectionKindOf :
    KnownZetaLikeProjection -> ZetaProjectionKind
  | KnownZetaLikeProjection.atlasDirichlet =>
      ZetaProjectionKind.dirichletAtlas
  | KnownZetaLikeProjection.constructiveEta =>
      ZetaProjectionKind.etaEvaluation
  | KnownZetaLikeProjection.zeroLedger =>
      ZetaProjectionKind.zeroLedger
  | KnownZetaLikeProjection.continuationWitness =>
      ZetaProjectionKind.continuationWitness
  | KnownZetaLikeProjection.generatedOntic =>
      ZetaProjectionKind.onticGeneratedPacket
  | KnownZetaLikeProjection.locatedBox =>
      ZetaProjectionKind.locatedBoxEvaluation

def knownZetaLikeProjections : List KnownZetaLikeProjection :=
  [ KnownZetaLikeProjection.atlasDirichlet,
    KnownZetaLikeProjection.constructiveEta,
    KnownZetaLikeProjection.zeroLedger,
    KnownZetaLikeProjection.continuationWitness,
    KnownZetaLikeProjection.generatedOntic,
    KnownZetaLikeProjection.locatedBox ]

def countNatCode (needle : Nat) : List Nat -> Nat
  | [] => 0
  | x :: xs =>
      match Nat.beq needle x with
      | true => Nat.succ (countNatCode needle xs)
      | false => countNatCode needle xs

def countKnownZetaProjection (needle : KnownZetaLikeProjection)
    (xs : List KnownZetaLikeProjection) : Nat :=
  countNatCode (knownZetaProjectionCode needle)
    (xs.map knownZetaProjectionCode)

def countZetaProjectionKind (needle : ZetaProjectionKind)
    (xs : List KnownZetaLikeProjection) : Nat :=
  countNatCode (zetaProjectionKindCode needle)
    (xs.map (fun row => zetaProjectionKindCode (zetaProjectionKindOf row)))

structure ZetaProjectionTaxonomyEntry where
  projection : KnownZetaLikeProjection
  kind : ZetaProjectionKind
  atlasProjection : AtlasProjection
  axes : OnticAxisTriple

def ZetaProjectionTaxonomyEntry.classified
    (entry : ZetaProjectionTaxonomyEntry) : Prop :=
  entry.kind = zetaProjectionKindOf entry.projection ∧
    entry.axes.Marked

def zetaProjectionTaxonomyEntry :
    KnownZetaLikeProjection -> ZetaProjectionTaxonomyEntry
  | KnownZetaLikeProjection.atlasDirichlet =>
      { projection := KnownZetaLikeProjection.atlasDirichlet
        kind := ZetaProjectionKind.dirichletAtlas
        atlasProjection := AtlasProjection.zetaDirichlet
        axes := canonicalOnticAxisTriple }
  | KnownZetaLikeProjection.constructiveEta =>
      { projection := KnownZetaLikeProjection.constructiveEta
        kind := ZetaProjectionKind.etaEvaluation
        atlasProjection := AtlasProjection.zetaDirichlet
        axes := canonicalOnticAxisTriple }
  | KnownZetaLikeProjection.zeroLedger =>
      { projection := KnownZetaLikeProjection.zeroLedger
        kind := ZetaProjectionKind.zeroLedger
        atlasProjection := AtlasProjection.zetaDirichlet
        axes := canonicalOnticAxisTriple }
  | KnownZetaLikeProjection.continuationWitness =>
      { projection := KnownZetaLikeProjection.continuationWitness
        kind := ZetaProjectionKind.continuationWitness
        atlasProjection := AtlasProjection.zetaDirichlet
        axes := canonicalOnticAxisTriple }
  | KnownZetaLikeProjection.generatedOntic =>
      { projection := KnownZetaLikeProjection.generatedOntic
        kind := ZetaProjectionKind.onticGeneratedPacket
        atlasProjection := AtlasProjection.zetaDirichlet
        axes := canonicalOnticAxisTriple }
  | KnownZetaLikeProjection.locatedBox =>
      { projection := KnownZetaLikeProjection.locatedBox
        kind := ZetaProjectionKind.locatedBoxEvaluation
        atlasProjection := AtlasProjection.zetaDirichlet
        axes := canonicalOnticAxisTriple }

def zetaProjectionTaxonomyRows : List ZetaProjectionTaxonomyEntry :=
  knownZetaLikeProjections.map zetaProjectionTaxonomyEntry

structure ZetaProjectionTaxonomy where
  atlas : UnifiedRelationAtlas
  entries : List ZetaProjectionTaxonomyEntry
  knownRows : List KnownZetaLikeProjection
  rowCount : KnownZetaLikeProjection -> Nat
  kindCount : ZetaProjectionKind -> Nat
  generatedPacket :
    BEDC.Derived.RHRoute.ZeroGenerationInitiality.RHFreeZeroSignature ->
      OnticPacket
  zeroLedgerSpec : BEDC.FKernel.Hist.BHist -> Prop
  continuationWitnessPacket :
    [BEDC.FKernel.Ask.AskSetup] ->
      [BEDC.FKernel.Package.PackageSetup] ->
        BEDC.FKernel.Hist.BHist ->
          BEDC.FKernel.Hist.BHist ->
            BEDC.FKernel.Hist.BHist ->
              BEDC.FKernel.Hist.BHist ->
                BEDC.FKernel.Hist.BHist ->
                  BEDC.FKernel.Hist.BHist ->
                    BEDC.FKernel.Hist.BHist ->
                      BEDC.FKernel.Hist.BHist ->
                        BEDC.FKernel.Hist.BHist ->
                          BEDC.FKernel.Hist.BHist ->
                            BEDC.FKernel.Hist.BHist ->
                              BEDC.FKernel.Bundle.ProbeBundle
                                  BEDC.FKernel.Ask.ProbeName ->
                                BEDC.FKernel.Package.Pkg ->
                                  Prop
  constructiveEvaluatorCarrier :
    (s : BEDC.Derived.RHRoute.ConstructiveZeta.RationalStripPoint) ->
      Type
  boxEvaluatorCarrier :
    (G : BEDC.Derived.RHRoute.ZetaBoxEvaluator.BoxGauge) ->
      (s : BEDC.Derived.RHRoute.ZetaBoxEvaluator.CriticalStripInput) ->
        Type
  inheritedChainCarrier :
    (G : BEDC.Derived.RHRoute.ZetaBoxEvaluator.BoxGauge) ->
      (s : BEDC.Derived.RHRoute.ZetaBoxEvaluator.CriticalStripInput) ->
        Type
  locatedZeroPredicate :
    BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex ->
      Prop

def zetaLikeProjectionTaxonomy : ZetaProjectionTaxonomy where
  atlas := unifiedRelationAtlas
  entries := zetaProjectionTaxonomyRows
  knownRows := knownZetaLikeProjections
  rowCount := fun row => countKnownZetaProjection row knownZetaLikeProjections
  kindCount := fun kind => countZetaProjectionKind kind knownZetaLikeProjections
  generatedPacket := generatedZetaOnticPacket
  zeroLedgerSpec := BEDC.Derived.ZetaZerosUp.ZetaZeroSourceSpec
  continuationWitnessPacket :=
    fun basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg =>
      BEDC.Derived.ZetaContinuationWitnessUp.ZetaContinuationWitnessPacket
        basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg
  constructiveEvaluatorCarrier :=
    fun s => BEDC.Derived.RHRoute.ConstructiveZeta.ConstructiveZetaEvaluator s
  boxEvaluatorCarrier :=
    fun G s => BEDC.Derived.RHRoute.ZetaBoxEvaluator.ZetaBoxEvaluator G s
  inheritedChainCarrier :=
    fun G s => BEDC.Derived.RHRoute.ZetaInheritedInvariants.ZetaConstructionChain G s
  locatedZeroPredicate :=
    fun s => BEDC.Derived.RHRoute.ZetaZeroLocated.ZetaZeroLocated s

def ZetaProjectionTaxonomy.CoversKnown
    (taxonomy : ZetaProjectionTaxonomy) : Prop :=
  (row : KnownZetaLikeProjection) -> taxonomy.rowCount row = 1

theorem zetaProjectionTaxonomyEntry_classified
    (row : KnownZetaLikeProjection) :
    (zetaProjectionTaxonomyEntry row).classified := by
  cases row with
  | atlasDirichlet =>
      exact ⟨rfl, canonicalOnticAxisTriple_marked⟩
  | constructiveEta =>
      exact ⟨rfl, canonicalOnticAxisTriple_marked⟩
  | zeroLedger =>
      exact ⟨rfl, canonicalOnticAxisTriple_marked⟩
  | continuationWitness =>
      exact ⟨rfl, canonicalOnticAxisTriple_marked⟩
  | generatedOntic =>
      exact ⟨rfl, canonicalOnticAxisTriple_marked⟩
  | locatedBox =>
      exact ⟨rfl, canonicalOnticAxisTriple_marked⟩

theorem zetaProjectionTaxonomy_rows_readback :
    zetaLikeProjectionTaxonomy.entries = zetaProjectionTaxonomyRows ∧
      zetaLikeProjectionTaxonomy.knownRows = knownZetaLikeProjections := by
  exact ⟨rfl, rfl⟩

theorem zetaProjectionTaxonomy_atlas_zeta_projection :
    zetaLikeProjectionTaxonomy.atlas.zetaDirichlet.projection =
      AtlasProjection.zetaDirichlet := by
  rfl

theorem zetaProjectionTaxonomy_atlas_axes_marked :
    zetaLikeProjectionTaxonomy.atlas.zetaDirichlet.axesMarked := by
  exact zetaDirichletEntry_axes_marked

theorem zetaProjectionTaxonomy_generated_packet_readback
    (signature :
      BEDC.Derived.RHRoute.ZeroGenerationInitiality.RHFreeZeroSignature) :
    zetaLikeProjectionTaxonomy.generatedPacket signature =
      generatedZetaOnticPacket signature := by
  rfl

theorem zetaProjectionTaxonomy_zero_ledger_readback :
    zetaLikeProjectionTaxonomy.zeroLedgerSpec =
      BEDC.Derived.ZetaZerosUp.ZetaZeroSourceSpec := by
  rfl

theorem zetaProjectionTaxonomy_continuation_witness_readback
    [BEDC.FKernel.Ask.AskSetup] [BEDC.FKernel.Package.PackageSetup]
    (basic eta analytic pole functional zeroLedger gamma transports routes
      provenance name : BEDC.FKernel.Hist.BHist)
    (bundle :
      BEDC.FKernel.Bundle.ProbeBundle BEDC.FKernel.Ask.ProbeName)
    (pkg : BEDC.FKernel.Package.Pkg) :
    zetaLikeProjectionTaxonomy.continuationWitnessPacket
        basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg =
      BEDC.Derived.ZetaContinuationWitnessUp.ZetaContinuationWitnessPacket
        basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg := by
  rfl

theorem zetaProjectionTaxonomy_constructive_evaluator_readback
    (s : BEDC.Derived.RHRoute.ConstructiveZeta.RationalStripPoint) :
    zetaLikeProjectionTaxonomy.constructiveEvaluatorCarrier s =
      BEDC.Derived.RHRoute.ConstructiveZeta.ConstructiveZetaEvaluator s := by
  rfl

theorem zetaProjectionTaxonomy_box_evaluator_readback
    (G : BEDC.Derived.RHRoute.ZetaBoxEvaluator.BoxGauge)
    (s : BEDC.Derived.RHRoute.ZetaBoxEvaluator.CriticalStripInput) :
    zetaLikeProjectionTaxonomy.boxEvaluatorCarrier G s =
      BEDC.Derived.RHRoute.ZetaBoxEvaluator.ZetaBoxEvaluator G s := by
  rfl

theorem zetaProjectionTaxonomy_inherited_chain_readback
    (G : BEDC.Derived.RHRoute.ZetaBoxEvaluator.BoxGauge)
    (s : BEDC.Derived.RHRoute.ZetaBoxEvaluator.CriticalStripInput) :
    zetaLikeProjectionTaxonomy.inheritedChainCarrier G s =
      BEDC.Derived.RHRoute.ZetaInheritedInvariants.ZetaConstructionChain G s := by
  rfl

theorem zetaProjectionTaxonomy_located_zero_readback
    (s : BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex) :
    zetaLikeProjectionTaxonomy.locatedZeroPredicate s =
      BEDC.Derived.RHRoute.ZetaZeroLocated.ZetaZeroLocated s := by
  rfl

theorem zetaProjectionTaxonomy_count_atlasDirichlet :
    zetaLikeProjectionTaxonomy.rowCount
      KnownZetaLikeProjection.atlasDirichlet = 1 := by
  rfl

theorem zetaProjectionTaxonomy_count_constructiveEta :
    zetaLikeProjectionTaxonomy.rowCount
      KnownZetaLikeProjection.constructiveEta = 1 := by
  rfl

theorem zetaProjectionTaxonomy_count_zeroLedger :
    zetaLikeProjectionTaxonomy.rowCount
      KnownZetaLikeProjection.zeroLedger = 1 := by
  rfl

theorem zetaProjectionTaxonomy_count_continuationWitness :
    zetaLikeProjectionTaxonomy.rowCount
      KnownZetaLikeProjection.continuationWitness = 1 := by
  rfl

theorem zetaProjectionTaxonomy_count_generatedOntic :
    zetaLikeProjectionTaxonomy.rowCount
      KnownZetaLikeProjection.generatedOntic = 1 := by
  rfl

theorem zetaProjectionTaxonomy_count_locatedBox :
    zetaLikeProjectionTaxonomy.rowCount
      KnownZetaLikeProjection.locatedBox = 1 := by
  rfl

theorem zetaProjectionTaxonomy_covers_known :
    zetaLikeProjectionTaxonomy.CoversKnown := by
  intro row
  cases row with
  | atlasDirichlet =>
      rfl
  | constructiveEta =>
      rfl
  | zeroLedger =>
      rfl
  | continuationWitness =>
      rfl
  | generatedOntic =>
      rfl
  | locatedBox =>
      rfl

theorem zetaProjectionTaxonomy_kind_counts :
    zetaLikeProjectionTaxonomy.kindCount ZetaProjectionKind.dirichletAtlas = 1 ∧
      zetaLikeProjectionTaxonomy.kindCount ZetaProjectionKind.etaEvaluation = 1 ∧
        zetaLikeProjectionTaxonomy.kindCount ZetaProjectionKind.zeroLedger = 1 ∧
          zetaLikeProjectionTaxonomy.kindCount
              ZetaProjectionKind.continuationWitness = 1 ∧
            zetaLikeProjectionTaxonomy.kindCount
                ZetaProjectionKind.onticGeneratedPacket = 1 ∧
              zetaLikeProjectionTaxonomy.kindCount
                  ZetaProjectionKind.locatedBoxEvaluation = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zetaProjectionTaxonomy_zeroLedger_entry_kind :
    (zetaProjectionTaxonomyEntry KnownZetaLikeProjection.zeroLedger).kind =
      ZetaProjectionKind.zeroLedger := by
  rfl

theorem zetaProjectionTaxonomy_continuation_entry_kind :
    (zetaProjectionTaxonomyEntry
        KnownZetaLikeProjection.continuationWitness).kind =
      ZetaProjectionKind.continuationWitness := by
  rfl

end BEDC.Derived.RHRoute.ZetaLikeProjectionTaxonomy
