import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedTowerCompressionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedTowerCompressionUp : Type where
  | mk (S T O F A M C L E R P N : BHist) : RealityConstrainedTowerCompressionUp
  deriving DecidableEq

def realityConstrainedTowerCompressionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedTowerCompressionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedTowerCompressionEncodeBHist h

def realityConstrainedTowerCompressionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedTowerCompressionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedTowerCompressionDecodeBHist tail)

private theorem RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedTowerCompressionToEventFlow :
    RealityConstrainedTowerCompressionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedTowerCompressionUp.mk S T O F A M C L E R P N =>
      [[BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist S,
        [BMark.b1, BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTowerCompressionEncodeBHist N]

private def realityConstrainedTowerCompressionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      realityConstrainedTowerCompressionEventAtDefault index rest

def realityConstrainedTowerCompressionFromEventFlow
    (ef : EventFlow) : Option RealityConstrainedTowerCompressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealityConstrainedTowerCompressionUp.mk
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 1 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 3 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 5 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 7 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 9 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 11 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 13 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 15 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 17 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 19 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 21 ef))
      (realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEventAtDefault 23 ef)))

private theorem RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealityConstrainedTowerCompressionUp,
      realityConstrainedTowerCompressionFromEventFlow
        (realityConstrainedTowerCompressionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T O F A M C L E R P N =>
      change
        some
          (RealityConstrainedTowerCompressionUp.mk
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist S))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist T))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist O))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist F))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist A))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist M))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist C))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist L))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist E))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist R))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist P))
            (realityConstrainedTowerCompressionDecodeBHist
              (realityConstrainedTowerCompressionEncodeBHist N))) =
          some (RealityConstrainedTowerCompressionUp.mk S T O F A M C L E R P N)
      rw [RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode S,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode T,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode O,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode F,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode A,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode M,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode C,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode L,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode E,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode R,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode P,
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode N]

private theorem RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_injective
    {x y : RealityConstrainedTowerCompressionUp} :
    realityConstrainedTowerCompressionToEventFlow x =
      realityConstrainedTowerCompressionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedTowerCompressionFromEventFlow
          (realityConstrainedTowerCompressionToEventFlow x) =
        realityConstrainedTowerCompressionFromEventFlow
          (realityConstrainedTowerCompressionToEventFlow y) :=
    congrArg realityConstrainedTowerCompressionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_round_trip y)))

private def realityConstrainedTowerCompressionFields :
    RealityConstrainedTowerCompressionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedTowerCompressionUp.mk S T O F A M C L E R P N =>
      [S, T, O, F, A, M, C, L, E, R, P, N]

private theorem RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealityConstrainedTowerCompressionUp,
      realityConstrainedTowerCompressionFields x =
        realityConstrainedTowerCompressionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 O1 F1 A1 M1 C1 L1 E1 R1 P1 N1 =>
      cases y with
      | mk S2 T2 O2 F2 A2 M2 C2 L2 E2 R2 P2 N2 =>
          cases hfields
          rfl

instance realityConstrainedTowerCompressionBHistCarrier :
    BHistCarrier RealityConstrainedTowerCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedTowerCompressionToEventFlow
  fromEventFlow := realityConstrainedTowerCompressionFromEventFlow

instance realityConstrainedTowerCompressionChapterTasteGate :
    ChapterTasteGate RealityConstrainedTowerCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedTowerCompressionFromEventFlow
        (realityConstrainedTowerCompressionToEventFlow x) = some x
    exact RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_injective heq)

instance realityConstrainedTowerCompressionFieldFaithful :
    FieldFaithful RealityConstrainedTowerCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedTowerCompressionFields
  field_faithful :=
    RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_fields

instance realityConstrainedTowerCompressionNontrivial :
    Nontrivial RealityConstrainedTowerCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedTowerCompressionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedTowerCompressionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedTowerCompressionDecodeBHist
        (realityConstrainedTowerCompressionEncodeBHist h) = h) ∧
      (∀ x : RealityConstrainedTowerCompressionUp,
        realityConstrainedTowerCompressionFromEventFlow
          (realityConstrainedTowerCompressionToEventFlow x) = some x) ∧
        (∀ x y : RealityConstrainedTowerCompressionUp,
          realityConstrainedTowerCompressionToEventFlow x =
            realityConstrainedTowerCompressionToEventFlow y → x = y) ∧
          realityConstrainedTowerCompressionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_decode,
      RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealityConstrainedTowerCompressionTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.RealityConstrainedTowerCompressionUp
