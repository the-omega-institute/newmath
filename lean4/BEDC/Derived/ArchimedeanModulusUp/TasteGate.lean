import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanModulusUp : Type where
  | mk (P D S Q E A H C N : BHist) : ArchimedeanModulusUp
  deriving DecidableEq

def archimedeanModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanModulusEncodeBHist h

def archimedeanModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanModulusDecodeBHist tail)

private theorem archimedeanModulus_decode_encode_bhist :
    ∀ h : BHist, archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def archimedeanModulusFields : ArchimedeanModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanModulusUp.mk P D S Q E A H C N => [P, D, S, Q, E, A, H, C, N]

def archimedeanModulusToEventFlow : ArchimedeanModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanModulusUp.mk P D S Q E A H C N =>
      [archimedeanModulusEncodeBHist P,
        archimedeanModulusEncodeBHist D,
        archimedeanModulusEncodeBHist S,
        archimedeanModulusEncodeBHist Q,
        archimedeanModulusEncodeBHist E,
        archimedeanModulusEncodeBHist A,
        archimedeanModulusEncodeBHist H,
        archimedeanModulusEncodeBHist C,
        archimedeanModulusEncodeBHist N]

private def archimedeanModulusRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => archimedeanModulusRawAt n rest

private def archimedeanModulusLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => archimedeanModulusLengthEq n rest

def archimedeanModulusFromEventFlow : EventFlow → Option ArchimedeanModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match archimedeanModulusLengthEq 9 flow with
      | true =>
          some
            (ArchimedeanModulusUp.mk
              (archimedeanModulusDecodeBHist (archimedeanModulusRawAt 0 flow))
              (archimedeanModulusDecodeBHist (archimedeanModulusRawAt 1 flow))
              (archimedeanModulusDecodeBHist (archimedeanModulusRawAt 2 flow))
              (archimedeanModulusDecodeBHist (archimedeanModulusRawAt 3 flow))
              (archimedeanModulusDecodeBHist (archimedeanModulusRawAt 4 flow))
              (archimedeanModulusDecodeBHist (archimedeanModulusRawAt 5 flow))
              (archimedeanModulusDecodeBHist (archimedeanModulusRawAt 6 flow))
              (archimedeanModulusDecodeBHist (archimedeanModulusRawAt 7 flow))
              (archimedeanModulusDecodeBHist (archimedeanModulusRawAt 8 flow)))
      | false => none

private theorem archimedeanModulus_round_trip :
    ∀ x : ArchimedeanModulusUp,
      archimedeanModulusFromEventFlow (archimedeanModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P D S Q E A H C N =>
      change
        some
          (ArchimedeanModulusUp.mk
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist P))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist D))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist S))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist Q))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist E))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist A))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist H))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist C))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist N))) =
          some (ArchimedeanModulusUp.mk P D S Q E A H C N)
      rw [archimedeanModulus_decode_encode_bhist P,
        archimedeanModulus_decode_encode_bhist D,
        archimedeanModulus_decode_encode_bhist S,
        archimedeanModulus_decode_encode_bhist Q,
        archimedeanModulus_decode_encode_bhist E,
        archimedeanModulus_decode_encode_bhist A,
        archimedeanModulus_decode_encode_bhist H,
        archimedeanModulus_decode_encode_bhist C,
        archimedeanModulus_decode_encode_bhist N]

private theorem archimedeanModulusToEventFlow_injective {x y : ArchimedeanModulusUp} :
    archimedeanModulusToEventFlow x = archimedeanModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanModulusFromEventFlow (archimedeanModulusToEventFlow x) =
        archimedeanModulusFromEventFlow (archimedeanModulusToEventFlow y) :=
    congrArg archimedeanModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (archimedeanModulus_round_trip x).symm
      (Eq.trans hread (archimedeanModulus_round_trip y)))

instance archimedeanModulusBHistCarrier : BHistCarrier ArchimedeanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanModulusToEventFlow
  fromEventFlow := archimedeanModulusFromEventFlow

instance archimedeanModulusChapterTasteGate :
    ChapterTasteGate ArchimedeanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change archimedeanModulusFromEventFlow (archimedeanModulusToEventFlow x) = some x
    exact archimedeanModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (archimedeanModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ArchimedeanModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanModulusChapterTasteGate

theorem ArchimedeanModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist h) = h) ∧
      archimedeanModulusFields
          (ArchimedeanModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨archimedeanModulus_decode_encode_bhist, rfl⟩

end BEDC.Derived.ArchimedeanModulusUp
