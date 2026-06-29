import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ItoIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ItoIntegralUp : Type where
  | mk (Omega X B Pi A Delta S M H C P N : BHist) : ItoIntegralUp
  deriving DecidableEq

def itoIntegralEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: itoIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: itoIntegralEncodeBHist h

def itoIntegralDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (itoIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (itoIntegralDecodeBHist tail)

private theorem ItoIntegralTasteGate_single_carrier_alignment_decode :
    forall h : BHist, itoIntegralDecodeBHist (itoIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def itoIntegralFields : ItoIntegralUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ItoIntegralUp.mk Omega X B Pi A Delta S M H C P N =>
      [Omega, X, B, Pi, A, Delta, S, M, H, C, P, N]

def itoIntegralToEventFlow : ItoIntegralUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (itoIntegralFields x).map itoIntegralEncodeBHist

private def itoIntegralRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => itoIntegralRawAt n rest

private def itoIntegralLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => itoIntegralLengthEq n rest

def itoIntegralFromEventFlow (flow : EventFlow) : Option ItoIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match itoIntegralLengthEq 12 flow with
  | true =>
      some
        (ItoIntegralUp.mk
          (itoIntegralDecodeBHist (itoIntegralRawAt 0 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 1 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 2 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 3 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 4 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 5 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 6 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 7 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 8 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 9 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 10 flow))
          (itoIntegralDecodeBHist (itoIntegralRawAt 11 flow)))
  | false => none

private theorem itoIntegral_round_trip :
    forall x : ItoIntegralUp,
      itoIntegralFromEventFlow (itoIntegralToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Omega X B Pi A Delta S M H C P N =>
      change
        some
          (ItoIntegralUp.mk
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist Omega))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist X))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist B))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist Pi))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist A))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist Delta))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist S))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist M))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist H))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist C))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist P))
            (itoIntegralDecodeBHist (itoIntegralEncodeBHist N))) =
          some (ItoIntegralUp.mk Omega X B Pi A Delta S M H C P N)
      rw [ItoIntegralTasteGate_single_carrier_alignment_decode Omega,
        ItoIntegralTasteGate_single_carrier_alignment_decode X,
        ItoIntegralTasteGate_single_carrier_alignment_decode B,
        ItoIntegralTasteGate_single_carrier_alignment_decode Pi,
        ItoIntegralTasteGate_single_carrier_alignment_decode A,
        ItoIntegralTasteGate_single_carrier_alignment_decode Delta,
        ItoIntegralTasteGate_single_carrier_alignment_decode S,
        ItoIntegralTasteGate_single_carrier_alignment_decode M,
        ItoIntegralTasteGate_single_carrier_alignment_decode H,
        ItoIntegralTasteGate_single_carrier_alignment_decode C,
        ItoIntegralTasteGate_single_carrier_alignment_decode P,
        ItoIntegralTasteGate_single_carrier_alignment_decode N]

private theorem itoIntegralToEventFlow_injective {x y : ItoIntegralUp} :
    itoIntegralToEventFlow x = itoIntegralToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      itoIntegralFromEventFlow (itoIntegralToEventFlow x) =
        itoIntegralFromEventFlow (itoIntegralToEventFlow y) :=
    congrArg itoIntegralFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (itoIntegral_round_trip x).symm (Eq.trans hread (itoIntegral_round_trip y)))

instance itoIntegralBHistCarrier : BHistCarrier ItoIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := itoIntegralToEventFlow
  fromEventFlow := itoIntegralFromEventFlow

instance itoIntegralChapterTasteGate : ChapterTasteGate ItoIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change itoIntegralFromEventFlow (itoIntegralToEventFlow x) = some x
    exact itoIntegral_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (itoIntegralToEventFlow_injective heq)

theorem ItoIntegralTasteGate_single_carrier_alignment :
    (forall h : BHist, itoIntegralDecodeBHist (itoIntegralEncodeBHist h) = h) ∧
    (forall x : ItoIntegralUp,
      itoIntegralFromEventFlow (itoIntegralToEventFlow x) = some x) ∧
    (forall x y : ItoIntegralUp,
      itoIntegralToEventFlow x = itoIntegralToEventFlow y -> x = y) ∧
    itoIntegralEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ItoIntegralTasteGate_single_carrier_alignment_decode
  · constructor
    · exact itoIntegral_round_trip
    · constructor
      · intro x y heq
        exact itoIntegralToEventFlow_injective heq
      · rfl

end BEDC.Derived.ItoIntegralUp
