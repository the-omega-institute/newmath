import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InducedCharacterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InducedCharacterUp : Type where
  | mk (G H Q V chi iota sigma kappa rho lambda P N : BHist) : InducedCharacterUp
  deriving DecidableEq

def inducedCharacterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inducedCharacterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inducedCharacterEncodeBHist h

def inducedCharacterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inducedCharacterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inducedCharacterDecodeBHist tail)

private theorem inducedCharacter_decode_encode_bhist :
    ∀ h : BHist, inducedCharacterDecodeBHist (inducedCharacterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def inducedCharacterToEventFlow : InducedCharacterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InducedCharacterUp.mk G H Q V chi iota sigma kappa rho lambda P N =>
      [inducedCharacterEncodeBHist G,
        inducedCharacterEncodeBHist H,
        inducedCharacterEncodeBHist Q,
        inducedCharacterEncodeBHist V,
        inducedCharacterEncodeBHist chi,
        inducedCharacterEncodeBHist iota,
        inducedCharacterEncodeBHist sigma,
        inducedCharacterEncodeBHist kappa,
        inducedCharacterEncodeBHist rho,
        inducedCharacterEncodeBHist lambda,
        inducedCharacterEncodeBHist P,
        inducedCharacterEncodeBHist N]

private def inducedCharacterRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => inducedCharacterRawAt n rest

private def inducedCharacterLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => inducedCharacterLengthEq n rest

def inducedCharacterFromEventFlow : EventFlow → Option InducedCharacterUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match inducedCharacterLengthEq 12 flow with
      | true =>
          some
            (InducedCharacterUp.mk
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 0 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 1 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 2 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 3 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 4 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 5 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 6 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 7 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 8 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 9 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 10 flow))
              (inducedCharacterDecodeBHist (inducedCharacterRawAt 11 flow)))
      | false => none

private theorem inducedCharacter_round_trip :
    ∀ x : InducedCharacterUp,
      inducedCharacterFromEventFlow (inducedCharacterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G H Q V chi iota sigma kappa rho lambda P N =>
      change
        some
          (InducedCharacterUp.mk
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist G))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist H))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist Q))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist V))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist chi))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist iota))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist sigma))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist kappa))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist rho))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist lambda))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist P))
            (inducedCharacterDecodeBHist (inducedCharacterEncodeBHist N))) =
          some (InducedCharacterUp.mk G H Q V chi iota sigma kappa rho lambda P N)
      rw [inducedCharacter_decode_encode_bhist G,
        inducedCharacter_decode_encode_bhist H,
        inducedCharacter_decode_encode_bhist Q,
        inducedCharacter_decode_encode_bhist V,
        inducedCharacter_decode_encode_bhist chi,
        inducedCharacter_decode_encode_bhist iota,
        inducedCharacter_decode_encode_bhist sigma,
        inducedCharacter_decode_encode_bhist kappa,
        inducedCharacter_decode_encode_bhist rho,
        inducedCharacter_decode_encode_bhist lambda,
        inducedCharacter_decode_encode_bhist P,
        inducedCharacter_decode_encode_bhist N]

private theorem inducedCharacterToEventFlow_injective {x y : InducedCharacterUp} :
    inducedCharacterToEventFlow x = inducedCharacterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inducedCharacterFromEventFlow (inducedCharacterToEventFlow x) =
        inducedCharacterFromEventFlow (inducedCharacterToEventFlow y) :=
    congrArg inducedCharacterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inducedCharacter_round_trip x).symm
      (Eq.trans hread (inducedCharacter_round_trip y)))

instance inducedCharacterBHistCarrier : BHistCarrier InducedCharacterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inducedCharacterToEventFlow
  fromEventFlow := inducedCharacterFromEventFlow

instance inducedCharacterChapterTasteGate : ChapterTasteGate InducedCharacterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inducedCharacterFromEventFlow (inducedCharacterToEventFlow x) = some x
    exact inducedCharacter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inducedCharacterToEventFlow_injective heq)

def taste_gate : ChapterTasteGate InducedCharacterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inducedCharacterChapterTasteGate

theorem InducedCharacterTasteGate_single_carrier_alignment :
    (∀ h : BHist, inducedCharacterDecodeBHist (inducedCharacterEncodeBHist h) = h) ∧
      inducedCharacterFromEventFlow
          (inducedCharacterToEventFlow
            (InducedCharacterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty)) =
        some
          (InducedCharacterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨inducedCharacter_decode_encode_bhist,
      inducedCharacter_round_trip
        (InducedCharacterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty)⟩

end BEDC.Derived.InducedCharacterUp
