import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyRepresentationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyRepresentationUp : Type where
  | mk (R Q J S M D X E H C P N : BHist) : LocatedCauchyRepresentationUp
  deriving DecidableEq

def locatedCauchyRepresentationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyRepresentationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyRepresentationEncodeBHist h

def locatedCauchyRepresentationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyRepresentationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyRepresentationDecodeBHist tail)

private theorem LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCauchyRepresentationDecodeBHist
          (locatedCauchyRepresentationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCauchyRepresentationFields : LocatedCauchyRepresentationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyRepresentationUp.mk R Q J S M D X E H C P N =>
      [R, Q, J, S, M, D, X, E, H, C, P, N]

def locatedCauchyRepresentationToEventFlow : LocatedCauchyRepresentationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedCauchyRepresentationFields x).map locatedCauchyRepresentationEncodeBHist

private def locatedCauchyRepresentationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCauchyRepresentationRawAt index rest

def locatedCauchyRepresentationFromEventFlow
    (flow : EventFlow) : Option LocatedCauchyRepresentationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCauchyRepresentationUp.mk
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 0 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 1 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 2 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 3 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 4 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 5 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 6 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 7 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 8 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 9 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 10 flow))
      (locatedCauchyRepresentationDecodeBHist (locatedCauchyRepresentationRawAt 11 flow)))

private theorem LocatedCauchyRepresentationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCauchyRepresentationUp,
      locatedCauchyRepresentationFromEventFlow
          (locatedCauchyRepresentationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R Q J S M D X E H C P N =>
      change
        some
            (LocatedCauchyRepresentationUp.mk
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist R))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist Q))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist J))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist S))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist M))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist D))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist X))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist E))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist H))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist C))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist P))
              (locatedCauchyRepresentationDecodeBHist
                (locatedCauchyRepresentationEncodeBHist N))) =
          some (LocatedCauchyRepresentationUp.mk R Q J S M D X E H C P N)
      rw [LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode R,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode Q,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode J,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode S,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode M,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode D,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode X,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode E,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode H,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode C,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode P,
        LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCauchyRepresentationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCauchyRepresentationUp} :
    locatedCauchyRepresentationToEventFlow x =
        locatedCauchyRepresentationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyRepresentationFromEventFlow
          (locatedCauchyRepresentationToEventFlow x) =
        locatedCauchyRepresentationFromEventFlow
          (locatedCauchyRepresentationToEventFlow y) :=
    congrArg locatedCauchyRepresentationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedCauchyRepresentationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCauchyRepresentationTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCauchyRepresentationBHistCarrier :
    BHistCarrier LocatedCauchyRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyRepresentationToEventFlow
  fromEventFlow := locatedCauchyRepresentationFromEventFlow

instance locatedCauchyRepresentationChapterTasteGate :
    ChapterTasteGate LocatedCauchyRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCauchyRepresentationFromEventFlow
          (locatedCauchyRepresentationToEventFlow x) =
        some x
    exact LocatedCauchyRepresentationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedCauchyRepresentationTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem LocatedCauchyRepresentationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        locatedCauchyRepresentationDecodeBHist
            (locatedCauchyRepresentationEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier LocatedCauchyRepresentationUp) ∧
        Nonempty (ChapterTasteGate LocatedCauchyRepresentationUp) ∧
          locatedCauchyRepresentationFields
              (LocatedCauchyRepresentationUp.mk
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedCauchyRepresentationTasteGate_single_carrier_alignment_decode,
      ⟨locatedCauchyRepresentationBHistCarrier⟩,
      ⟨locatedCauchyRepresentationChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedCauchyRepresentationUp
