import BEDC.Derived.TotallyBoundedIntervalUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotallyBoundedIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def totallyBoundedIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totallyBoundedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totallyBoundedIntervalEncodeBHist h

def totallyBoundedIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totallyBoundedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totallyBoundedIntervalDecodeBHist tail)

private theorem totallyBoundedIntervalDecode_encode :
    ∀ h : BHist,
      totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def totallyBoundedIntervalToEventFlow : BEDC.Derived.TotallyBoundedIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.TotallyBoundedIntervalUp.mk
      lowerEndpoint upperEndpoint locatedMembership dyadicMeshRadius regSeqRatReadback
      meshSchedule finiteNet realSeal transport replay provenance localNameCert =>
      [totallyBoundedIntervalEncodeBHist lowerEndpoint,
        totallyBoundedIntervalEncodeBHist upperEndpoint,
        totallyBoundedIntervalEncodeBHist locatedMembership,
        totallyBoundedIntervalEncodeBHist dyadicMeshRadius,
        totallyBoundedIntervalEncodeBHist regSeqRatReadback,
        totallyBoundedIntervalEncodeBHist meshSchedule,
        totallyBoundedIntervalEncodeBHist finiteNet,
        totallyBoundedIntervalEncodeBHist realSeal,
        totallyBoundedIntervalEncodeBHist transport,
        totallyBoundedIntervalEncodeBHist replay,
        totallyBoundedIntervalEncodeBHist provenance,
        totallyBoundedIntervalEncodeBHist localNameCert]

private def totallyBoundedIntervalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => totallyBoundedIntervalEventAt index rest

def totallyBoundedIntervalFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.TotallyBoundedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.TotallyBoundedIntervalUp.mk
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 0 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 1 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 2 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 3 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 4 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 5 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 6 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 7 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 8 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 9 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 10 ef))
      (totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEventAt 11 ef)))

private theorem totallyBoundedInterval_round_trip :
    ∀ x : BEDC.Derived.TotallyBoundedIntervalUp,
      totallyBoundedIntervalFromEventFlow
        (totallyBoundedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lowerEndpoint upperEndpoint locatedMembership dyadicMeshRadius regSeqRatReadback
      meshSchedule finiteNet realSeal transport replay provenance localNameCert =>
      change
        some
          (BEDC.Derived.TotallyBoundedIntervalUp.mk
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist lowerEndpoint))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist upperEndpoint))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist locatedMembership))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist dyadicMeshRadius))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist regSeqRatReadback))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist meshSchedule))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist finiteNet))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist realSeal))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist transport))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist replay))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist provenance))
            (totallyBoundedIntervalDecodeBHist
              (totallyBoundedIntervalEncodeBHist localNameCert))) =
          some
            (BEDC.Derived.TotallyBoundedIntervalUp.mk
              lowerEndpoint upperEndpoint locatedMembership dyadicMeshRadius regSeqRatReadback
              meshSchedule finiteNet realSeal transport replay provenance localNameCert)
      rw [totallyBoundedIntervalDecode_encode lowerEndpoint,
        totallyBoundedIntervalDecode_encode upperEndpoint,
        totallyBoundedIntervalDecode_encode locatedMembership,
        totallyBoundedIntervalDecode_encode dyadicMeshRadius,
        totallyBoundedIntervalDecode_encode regSeqRatReadback,
        totallyBoundedIntervalDecode_encode meshSchedule,
        totallyBoundedIntervalDecode_encode finiteNet,
        totallyBoundedIntervalDecode_encode realSeal,
        totallyBoundedIntervalDecode_encode transport,
        totallyBoundedIntervalDecode_encode replay,
        totallyBoundedIntervalDecode_encode provenance,
        totallyBoundedIntervalDecode_encode localNameCert]

private theorem totallyBoundedIntervalToEventFlow_injective
    {x y : BEDC.Derived.TotallyBoundedIntervalUp} :
    totallyBoundedIntervalToEventFlow x = totallyBoundedIntervalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totallyBoundedIntervalFromEventFlow (totallyBoundedIntervalToEventFlow x) =
        totallyBoundedIntervalFromEventFlow (totallyBoundedIntervalToEventFlow y) :=
    congrArg totallyBoundedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (totallyBoundedInterval_round_trip x).symm
      (Eq.trans hread (totallyBoundedInterval_round_trip y)))

instance totallyBoundedIntervalBHistCarrier :
    BHistCarrier BEDC.Derived.TotallyBoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totallyBoundedIntervalToEventFlow
  fromEventFlow := totallyBoundedIntervalFromEventFlow

instance totallyBoundedIntervalChapterTasteGate :
    ChapterTasteGate BEDC.Derived.TotallyBoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change totallyBoundedIntervalFromEventFlow (totallyBoundedIntervalToEventFlow x) = some x
    exact totallyBoundedInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (totallyBoundedIntervalToEventFlow_injective heq)

theorem TotallyBoundedIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, totallyBoundedIntervalDecodeBHist (totallyBoundedIntervalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BEDC.Derived.TotallyBoundedIntervalUp) ∧
        Nonempty (ChapterTasteGate BEDC.Derived.TotallyBoundedIntervalUp) ∧
          totallyBoundedIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨totallyBoundedIntervalDecode_encode,
      ⟨totallyBoundedIntervalBHistCarrier⟩,
      ⟨totallyBoundedIntervalChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.TotallyBoundedIntervalUp
