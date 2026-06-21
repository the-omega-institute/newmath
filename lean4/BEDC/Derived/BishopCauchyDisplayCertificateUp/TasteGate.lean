import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyDisplayCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyDisplayCertificateUp : Type where
  | mk (Q M W T R D E H C P N : BHist) : BishopCauchyDisplayCertificateUp
  deriving DecidableEq

def bishopCauchyDisplayCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyDisplayCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyDisplayCertificateEncodeBHist h

def bishopCauchyDisplayCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyDisplayCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyDisplayCertificateDecodeBHist tail)

private theorem BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyDisplayCertificateFields :
    BishopCauchyDisplayCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyDisplayCertificateUp.mk Q M W T R D E H C P N =>
      [Q, M, W, T, R, D, E, H, C, P, N]

def bishopCauchyDisplayCertificateToEventFlow :
    BishopCauchyDisplayCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopCauchyDisplayCertificateFields x).map
        bishopCauchyDisplayCertificateEncodeBHist

private def bishopCauchyDisplayCertificateEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyDisplayCertificateEventAtDefault index rest

def bishopCauchyDisplayCertificateFromEventFlow (ef : EventFlow) :
    Option BishopCauchyDisplayCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyDisplayCertificateUp.mk
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 0 ef))
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 1 ef))
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 2 ef))
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 3 ef))
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 4 ef))
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 5 ef))
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 6 ef))
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 7 ef))
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 8 ef))
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 9 ef))
      (bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEventAtDefault 10 ef)))

private theorem BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_round_trip
    (x : BishopCauchyDisplayCertificateUp) :
    bishopCauchyDisplayCertificateFromEventFlow
      (bishopCauchyDisplayCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q M W T R D E H C P N =>
      change
        some
          (BishopCauchyDisplayCertificateUp.mk
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist Q))
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist M))
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist W))
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist T))
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist R))
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist D))
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist E))
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist H))
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist C))
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist P))
            (bishopCauchyDisplayCertificateDecodeBHist
              (bishopCauchyDisplayCertificateEncodeBHist N))) =
          some (BishopCauchyDisplayCertificateUp.mk Q M W T R D E H C P N)
      rw [BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode Q,
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode M,
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode W,
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode T,
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode R,
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode D,
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode E,
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode H,
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode C,
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode P,
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode N]

private theorem
    BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCauchyDisplayCertificateUp} :
    bishopCauchyDisplayCertificateToEventFlow x =
      bishopCauchyDisplayCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyDisplayCertificateFromEventFlow
          (bishopCauchyDisplayCertificateToEventFlow x) =
        bishopCauchyDisplayCertificateFromEventFlow
          (bishopCauchyDisplayCertificateToEventFlow y) :=
    congrArg bishopCauchyDisplayCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_round_trip y)))

instance bishopCauchyDisplayCertificateBHistCarrier :
    BHistCarrier BishopCauchyDisplayCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyDisplayCertificateToEventFlow
  fromEventFlow := bishopCauchyDisplayCertificateFromEventFlow

instance bishopCauchyDisplayCertificateChapterTasteGate :
    ChapterTasteGate BishopCauchyDisplayCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyDisplayCertificateFromEventFlow
        (bishopCauchyDisplayCertificateToEventFlow x) = some x
    exact BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCauchyDisplayCertificateDecodeBHist
        (bishopCauchyDisplayCertificateEncodeBHist h) = h) ∧
      (∀ x : BishopCauchyDisplayCertificateUp,
        bishopCauchyDisplayCertificateFromEventFlow
          (bishopCauchyDisplayCertificateToEventFlow x) = some x) ∧
        (∀ x y : BishopCauchyDisplayCertificateUp,
          bishopCauchyDisplayCertificateToEventFlow x =
            bishopCauchyDisplayCertificateToEventFlow y → x = y) ∧
          bishopCauchyDisplayCertificateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_decode_encode,
      BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopCauchyDisplayCertificateTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.BishopCauchyDisplayCertificateUp
