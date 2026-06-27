import BEDC.Derived.ApophaticFarEndSocketUp.TasteGate
import BEDC.Derived.LocatedReal.RatMetricKit
import BEDC.Derived.NonCollapseInvariantUp
import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TranscendentalFarEndUp

open BEDC.Derived.LocatedReal
open BEDC.Derived.NonCollapseInvariantUp
open BEDC.Derived.RationalUp
open BEDC.FKernel.Hist

/-- 位于过程: 每个可读阶段给出一个 located real。 -/
structure LocatedProcess (K : RatMetricKit) where
  sample : Nat → LReal K

def LocatedProcess.stage {K : RatMetricKit} (p : LocatedProcess K) (n : Nat) :
    LReal K :=
  p.sample n

def RatNonzero (q : RatNum) : Prop :=
  RatEq q ratZero → False

def RelationSupportNonzero (coefficients : List RatNum) : Prop :=
  ∃ q : RatNum, List.Mem q coefficients ∧ RatNonzero q

/--
有限代数关系是有限系数行、度数上界、非零支撑以及对位于过程的读法。
读法是关系行的一部分; 本文件只验证由这些行推出的边界性质。
-/
structure FiniteAlgebraicRelation (K : RatMetricKit) where
  coefficients : List RatNum
  degreeBound : Nat
  support_nonzero : RelationSupportNonzero coefficients
  evaluate : LocatedProcess K → LReal K

def FiniteAlgebraicRelation.coefficientCount {K : RatMetricKit}
    (relation : FiniteAlgebraicRelation K) : Nat :=
  relation.coefficients.length

theorem FiniteAlgebraicRelation.has_nonzero_coefficient {K : RatMetricKit}
    (relation : FiniteAlgebraicRelation K) :
    ∃ q : RatNum, List.Mem q relation.coefficients ∧ RatNonzero q :=
  relation.support_nonzero

def SatisfiesFiniteAlgebraicRelation {K : RatMetricKit}
    (process : LocatedProcess K) (relation : FiniteAlgebraicRelation K) : Prop :=
  LRealEq K (relation.evaluate process) (ratToLReal K ratZero)

def NoFiniteAlgebraicRelation {K : RatMetricKit}
    (process : LocatedProcess K) : Prop :=
  ∀ relation : FiniteAlgebraicRelation K,
    SatisfiesFiniteAlgebraicRelation process relation → False

theorem NoFiniteAlgebraicRelation.rejects {K : RatMetricKit}
    {process : LocatedProcess K}
    (noRelation : NoFiniteAlgebraicRelation process)
    (relation : FiniteAlgebraicRelation K) :
    SatisfiesFiniteAlgebraicRelation process relation → False :=
  noRelation relation

def RelationListSatisfied {K : RatMetricKit}
    (process : LocatedProcess K) (relations : List (FiniteAlgebraicRelation K)) :
    Prop :=
  ∃ relation : FiniteAlgebraicRelation K,
    List.Mem relation relations ∧
      SatisfiesFiniteAlgebraicRelation process relation

theorem NoFiniteAlgebraicRelation.no_relation_list {K : RatMetricKit}
    {process : LocatedProcess K}
    (noRelation : NoFiniteAlgebraicRelation process)
    (relations : List (FiniteAlgebraicRelation K)) :
    RelationListSatisfied process relations → False := by
  intro satisfied
  cases satisfied with
  | intro relation relationData =>
      exact noRelation relation relationData.right

/--
超越过程: 一个位于过程, 加上对每条有限非零代数关系的拒绝。
存在性不在这里伪造; 使用者必须提供真实的关系拒绝数据。
-/
structure TranscendentalProcess (K : RatMetricKit) where
  process : LocatedProcess K
  no_finite_algebraic_relation : NoFiniteAlgebraicRelation process

theorem TranscendentalProcess.rejects_relation {K : RatMetricKit}
    (transcendental : TranscendentalProcess K)
    (relation : FiniteAlgebraicRelation K) :
    SatisfiesFiniteAlgebraicRelation transcendental.process relation → False :=
  transcendental.no_finite_algebraic_relation relation

theorem TranscendentalProcess.rejects_relation_list {K : RatMetricKit}
    (transcendental : TranscendentalProcess K)
    (relations : List (FiniteAlgebraicRelation K)) :
    RelationListSatisfied transcendental.process relations → False :=
  NoFiniteAlgebraicRelation.no_relation_list
    transcendental.no_finite_algebraic_relation relations

/--
有限代数包络只通过有限 List 记录关系; `contains_sound` 要求任何容纳声明
都读回为某条已列关系的满足。
-/
structure FiniteAlgebraicEnvelope (K : RatMetricKit) where
  relations : List (FiniteAlgebraicRelation K)
  relations_nodup : relations.Nodup
  contains : LocatedProcess K → Prop
  contains_sound :
    ∀ {process : LocatedProcess K}, contains process →
      RelationListSatisfied process relations

theorem TranscendentalProcess.no_finite_algebraic_envelope_contains
    {K : RatMetricKit}
    (transcendental : TranscendentalProcess K)
    (envelope : FiniteAlgebraicEnvelope K) :
    envelope.contains transcendental.process → False := by
  intro contained
  exact transcendental.rejects_relation_list envelope.relations
    (envelope.contains_sound contained)

def ConstantLocatedProcess {K : RatMetricKit} (point : LReal K) :
    LocatedProcess K where
  sample := fun _ => point

def RationalStageRetraction {K : RatMetricKit}
    (process : LocatedProcess K) : Prop :=
  ∃ q : RatNum, LRealEq K (process.sample 0) (ratToLReal K q)

theorem NonCollapseWitness.no_constant_process_rational_stage_retraction
    {K : RatMetricKit}
    (separating : SeparatingRatMetricKit K)
    (witness : NonCollapseWitness K) :
    RationalStageRetraction (ConstantLocatedProcess witness.point) → False := by
  intro retraction
  exact NonCollapseWitness_no_rat_retraction separating witness retraction

/-- apophatic far-end 只导出 socket 行, 不导出 located-process 元素。 -/
inductive TranscendentalFarEndSocket : Type where
  | mk
      (socket process relationBoundary envelopeBoundary apophaticBoundary ledger
        transport route provenance localName : BHist) :
      TranscendentalFarEndSocket
  deriving DecidableEq

def farEndSocketFields : TranscendentalFarEndSocket → List BHist
  | TranscendentalFarEndSocket.mk socket process relationBoundary envelopeBoundary
      apophaticBoundary ledger transport route provenance localName =>
      [socket, process, relationBoundary, envelopeBoundary, apophaticBoundary, ledger,
        transport, route, provenance, localName]

def farEndSocketElementProjection
    (_K : RatMetricKit) (_socket : TranscendentalFarEndSocket) :
    Option (LocatedProcess _K) :=
  none

theorem farEndSocket_no_element_projection
    (K : RatMetricKit) (socket : TranscendentalFarEndSocket) :
    farEndSocketElementProjection K socket = none :=
  rfl

theorem farEndSocket_fields
    {socket process relationBoundary envelopeBoundary apophaticBoundary ledger
      transport route provenance localName : BHist} :
    farEndSocketFields
        (TranscendentalFarEndSocket.mk socket process relationBoundary envelopeBoundary
          apophaticBoundary ledger transport route provenance localName) =
      [socket, process, relationBoundary, envelopeBoundary, apophaticBoundary, ledger,
        transport, route, provenance, localName] :=
  rfl

theorem farEndSocket_apophatic_boundary
    {socket process relationBoundary envelopeBoundary apophaticBoundary ledger
      transport route provenance localName : BHist} :
    farEndSocketFields
        (TranscendentalFarEndSocket.mk socket process relationBoundary envelopeBoundary
          apophaticBoundary ledger transport route provenance localName) =
      [socket, process, relationBoundary, envelopeBoundary, apophaticBoundary, ledger,
        transport, route, provenance, localName] ∧
      farEndSocketElementProjection
        RatMetricKitConcrete
        (TranscendentalFarEndSocket.mk socket process relationBoundary envelopeBoundary
          apophaticBoundary ledger transport route provenance localName) = none := by
  constructor
  · rfl
  · rfl

end BEDC.Derived.TranscendentalFarEndUp
