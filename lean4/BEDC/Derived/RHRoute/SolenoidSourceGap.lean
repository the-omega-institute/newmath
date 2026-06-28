import BEDC.Derived.RHRoute.FarEndUnityNormalization
import BEDC.Derived.RHRoute.OnticBoundaryLedger
import BEDC.Derived.RHRoute.PrimeSkewDefect

namespace BEDC.Derived.RHRoute.SolenoidSourceGap

abbrev RatComplex :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.RatComplex

abbrev NontrivialZetaZero :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.NontrivialZetaZero

abbrev PrimeWindow :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

abbrev PrimeResonanceFamily :=
  BEDC.Derived.RHRoute.OnticBoundaryLedger.PrimeResonanceFamily

abbrev SolenoidLeeYangResonanceRows :=
  BEDC.Derived.RHRoute.OnticBoundaryLedger.SolenoidLeeYangResonanceRows

abbrev PrimeWindowNormalization :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.PrimeWindowNormalization

/--
源机制只保存 vision 要求的同一族数据。Lee--Yang 圆定理、Rouche 分析和
每个零点的存在性不在这里被构造。
-/
structure DominantSolenoidSource (s : RatComplex) where
  family : PrimeResonanceFamily
  zero : NontrivialZetaZero s
  dominant : Prop
  tailBound : Prop
  roucheGap : Prop
  solenoidCompatible : Prop
  farEndEnergyBound : Prop
  dominantWitness : dominant
  tailBoundWitness : tailBound
  roucheGapWitness : roucheGap
  solenoidCompatibleWitness : solenoidCompatible
  farEndEnergyBoundWitness : farEndEnergyBound

def DominantSolenoidSource.zeroRelevant
    {s : RatComplex} (_source : DominantSolenoidSource s) : Prop :=
  NontrivialZetaZero s

theorem DominantSolenoidSource.zero_relevant
    {s : RatComplex} (source : DominantSolenoidSource s) :
    source.zeroRelevant := by
  exact source.zero

theorem DominantSolenoidSource.has_dominance
    {s : RatComplex} (source : DominantSolenoidSource s) :
    source.dominant := by
  exact source.dominantWitness

theorem DominantSolenoidSource.has_tail_bound
    {s : RatComplex} (source : DominantSolenoidSource s) :
    source.tailBound := by
  exact source.tailBoundWitness

theorem DominantSolenoidSource.has_rouche_gap
    {s : RatComplex} (source : DominantSolenoidSource s) :
    source.roucheGap := by
  exact source.roucheGapWitness

theorem DominantSolenoidSource.has_solenoid_compatibility
    {s : RatComplex} (source : DominantSolenoidSource s) :
    source.solenoidCompatible := by
  exact source.solenoidCompatibleWitness

theorem DominantSolenoidSource.has_far_end_energy_bound
    {s : RatComplex} (source : DominantSolenoidSource s) :
    source.farEndEnergyBound := by
  exact source.farEndEnergyBoundWitness

structure SourceConstructor where
  build :
    (s : RatComplex) -> NontrivialZetaZero s -> DominantSolenoidSource s

def SourceConstructor.sourceExists
    (constructor : SourceConstructor) (s : RatComplex)
    (zero : NontrivialZetaZero s) :
    Exists (fun source : DominantSolenoidSource s => source.zero = zero) :=
  Exists.intro (constructor.build s zero) rfl

/--
source gap packet 是“每个临界带零点都有源族”的有限 carrier 形状。
它不是 RH 结论, 也不含 Lee--Yang 复分析证明。
-/
structure SolenoidSourceGapPacket where
  sourceFor :
    (s : RatComplex) -> NontrivialZetaZero s -> DominantSolenoidSource s

def sourceGapPacket_from_constructor
    (constructor : SourceConstructor) : SolenoidSourceGapPacket where
  sourceFor := constructor.build

theorem sourceGapPacket_from_constructor_projects
    (constructor : SourceConstructor) (s : RatComplex)
    (zero : NontrivialZetaZero s) :
    (sourceGapPacket_from_constructor constructor).sourceFor s zero =
      constructor.build s zero := by
  rfl

theorem sourceGapPacket_source_zero_relevant
    (packet : SolenoidSourceGapPacket) (s : RatComplex)
    (zero : NontrivialZetaZero s) :
    (packet.sourceFor s zero).zeroRelevant := by
  exact (packet.sourceFor s zero).zero_relevant

structure LocatedSourcePacket where
  point : RatComplex
  zero : NontrivialZetaZero point
  source : DominantSolenoidSource point
  source_zero_eq : source.zero = zero

def SolenoidSourceGapPacket.locate
    (packet : SolenoidSourceGapPacket) (s : RatComplex)
    (zero : NontrivialZetaZero s) : LocatedSourcePacket where
  point := s
  zero := zero
  source := packet.sourceFor s zero
  source_zero_eq := rfl

theorem SolenoidSourceGapPacket.locate_point
    (packet : SolenoidSourceGapPacket) (s : RatComplex)
    (zero : NontrivialZetaZero s) :
    (packet.locate s zero).point = s := by
  rfl

theorem SolenoidSourceGapPacket.locate_source_zero
    (packet : SolenoidSourceGapPacket) (s : RatComplex)
    (zero : NontrivialZetaZero s) :
    (packet.locate s zero).source.zero = zero := by
  rfl

def SourceGapResolvedBy
    (constructor : SourceConstructor) (packet : SolenoidSourceGapPacket) :
    Prop :=
  (s : RatComplex) ->
    (zero : NontrivialZetaZero s) ->
      packet.sourceFor s zero = constructor.build s zero

theorem sourceGapPacket_resolves_constructor
    (constructor : SourceConstructor) :
    SourceGapResolvedBy constructor (sourceGapPacket_from_constructor constructor) := by
  intro s zero
  rfl

structure DominantSourceToBoundaryRows where
  sourcePacket : SolenoidSourceGapPacket
  boundaryRows : SolenoidLeeYangResonanceRows
  source_to_finite_compatibility :
    (s : RatComplex) ->
      (zero : NontrivialZetaZero s) ->
        (W : PrimeWindow) ->
          boundaryRows.solenoidWindow W ->
            boundaryRows.finiteResonanceCompatibility W s

def DominantSourceToBoundaryRows.finiteCompatibilityAt
    (rows : DominantSourceToBoundaryRows) (s : RatComplex)
    (zero : NontrivialZetaZero s) (W : PrimeWindow)
    (window : rows.boundaryRows.solenoidWindow W) :
    rows.boundaryRows.finiteResonanceCompatibility W s :=
  rows.source_to_finite_compatibility s zero W window

theorem dominant_source_boundary_uses_same_zero
    (rows : DominantSourceToBoundaryRows) (s : RatComplex)
    (zero : NontrivialZetaZero s) :
    (rows.sourcePacket.sourceFor s zero).zeroRelevant := by
  exact sourceGapPacket_source_zero_relevant rows.sourcePacket s zero

end BEDC.Derived.RHRoute.SolenoidSourceGap
