import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRegularRealRepresentationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRegularRealRepresentationUp : Type where
  | mk (W Q D K E H C P N : BHist) : BishopRegularRealRepresentationUp
  deriving DecidableEq

def bishopRegularRealRepresentationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRegularRealRepresentationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRegularRealRepresentationEncodeBHist h

def bishopRegularRealRepresentationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRegularRealRepresentationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRegularRealRepresentationDecodeBHist tail)

private theorem BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopRegularRealRepresentationDecodeBHist
          (bishopRegularRealRepresentationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRegularRealRepresentationFields :
    BishopRegularRealRepresentationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularRealRepresentationUp.mk W Q D K E H C P N =>
      [W, Q, D, K, E, H, C, P, N]

def bishopRegularRealRepresentationToEventFlow :
    BishopRegularRealRepresentationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map bishopRegularRealRepresentationEncodeBHist
        (bishopRegularRealRepresentationFields x)

private def bishopRegularRealRepresentationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRegularRealRepresentationEventAt index rest

def bishopRegularRealRepresentationFromEventFlow :
    EventFlow → Option BishopRegularRealRepresentationUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BishopRegularRealRepresentationUp.mk
          (bishopRegularRealRepresentationDecodeBHist
            (bishopRegularRealRepresentationEventAt 0 ef))
          (bishopRegularRealRepresentationDecodeBHist
            (bishopRegularRealRepresentationEventAt 1 ef))
          (bishopRegularRealRepresentationDecodeBHist
            (bishopRegularRealRepresentationEventAt 2 ef))
          (bishopRegularRealRepresentationDecodeBHist
            (bishopRegularRealRepresentationEventAt 3 ef))
          (bishopRegularRealRepresentationDecodeBHist
            (bishopRegularRealRepresentationEventAt 4 ef))
          (bishopRegularRealRepresentationDecodeBHist
            (bishopRegularRealRepresentationEventAt 5 ef))
          (bishopRegularRealRepresentationDecodeBHist
            (bishopRegularRealRepresentationEventAt 6 ef))
          (bishopRegularRealRepresentationDecodeBHist
            (bishopRegularRealRepresentationEventAt 7 ef))
          (bishopRegularRealRepresentationDecodeBHist
            (bishopRegularRealRepresentationEventAt 8 ef)))

private theorem BishopRegularRealRepresentationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopRegularRealRepresentationUp,
      bishopRegularRealRepresentationFromEventFlow
          (bishopRegularRealRepresentationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W Q D K E H C P N =>
      change
        some
          (BishopRegularRealRepresentationUp.mk
            (bishopRegularRealRepresentationDecodeBHist
              (bishopRegularRealRepresentationEncodeBHist W))
            (bishopRegularRealRepresentationDecodeBHist
              (bishopRegularRealRepresentationEncodeBHist Q))
            (bishopRegularRealRepresentationDecodeBHist
              (bishopRegularRealRepresentationEncodeBHist D))
            (bishopRegularRealRepresentationDecodeBHist
              (bishopRegularRealRepresentationEncodeBHist K))
            (bishopRegularRealRepresentationDecodeBHist
              (bishopRegularRealRepresentationEncodeBHist E))
            (bishopRegularRealRepresentationDecodeBHist
              (bishopRegularRealRepresentationEncodeBHist H))
            (bishopRegularRealRepresentationDecodeBHist
              (bishopRegularRealRepresentationEncodeBHist C))
            (bishopRegularRealRepresentationDecodeBHist
              (bishopRegularRealRepresentationEncodeBHist P))
            (bishopRegularRealRepresentationDecodeBHist
              (bishopRegularRealRepresentationEncodeBHist N))) =
          some (BishopRegularRealRepresentationUp.mk W Q D K E H C P N)
      rw [BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode W,
        BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode Q,
        BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode D,
        BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode K,
        BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode E,
        BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode H,
        BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode C,
        BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode P,
        BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode N]

private theorem BishopRegularRealRepresentationTasteGate_single_carrier_alignment_injective
    {x y : BishopRegularRealRepresentationUp} :
    bishopRegularRealRepresentationToEventFlow x =
        bishopRegularRealRepresentationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRegularRealRepresentationFromEventFlow
          (bishopRegularRealRepresentationToEventFlow x) =
        bishopRegularRealRepresentationFromEventFlow
          (bishopRegularRealRepresentationToEventFlow y) :=
    congrArg bishopRegularRealRepresentationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRegularRealRepresentationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRegularRealRepresentationTasteGate_single_carrier_alignment_round_trip y)))

instance bishopRegularRealRepresentationBHistCarrier :
    BHistCarrier BishopRegularRealRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRegularRealRepresentationToEventFlow
  fromEventFlow := bishopRegularRealRepresentationFromEventFlow

instance bishopRegularRealRepresentationChapterTasteGate :
    ChapterTasteGate BishopRegularRealRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRegularRealRepresentationFromEventFlow
          (bishopRegularRealRepresentationToEventFlow x) =
        some x
    exact BishopRegularRealRepresentationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopRegularRealRepresentationTasteGate_single_carrier_alignment_injective heq)

theorem BishopRegularRealRepresentationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopRegularRealRepresentationDecodeBHist
          (bishopRegularRealRepresentationEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier BishopRegularRealRepresentationUp) ∧
        Nonempty (ChapterTasteGate BishopRegularRealRepresentationUp) ∧
          bishopRegularRealRepresentationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BishopRegularRealRepresentationTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ⟨bishopRegularRealRepresentationBHistCarrier⟩
    · constructor
      · exact ⟨bishopRegularRealRepresentationChapterTasteGate⟩
      · rfl

end BEDC.Derived.BishopRegularRealRepresentationUp.TasteGate
