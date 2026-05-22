import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SternBrocotUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SternBrocotUp : Type where
  | mk (A L U M F B Q R H C P N : BHist) : SternBrocotUp
  deriving DecidableEq

def sternBrocotEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sternBrocotEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sternBrocotEncodeBHist h

def sternBrocotDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sternBrocotDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sternBrocotDecodeBHist tail)

private theorem SternBrocotUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, sternBrocotDecodeBHist (sternBrocotEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sternBrocotFields : SternBrocotUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SternBrocotUp.mk A L U M F B Q R H C P N => [A, L, U, M, F, B, Q, R, H, C, P, N]

def sternBrocotToEventFlow : SternBrocotUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sternBrocotFields x).map sternBrocotEncodeBHist

private def sternBrocotDecodePacket
    (A L U M F B Q R H C P N : RawEvent) : SternBrocotUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SternBrocotUp.mk
    (sternBrocotDecodeBHist A)
    (sternBrocotDecodeBHist L)
    (sternBrocotDecodeBHist U)
    (sternBrocotDecodeBHist M)
    (sternBrocotDecodeBHist F)
    (sternBrocotDecodeBHist B)
    (sternBrocotDecodeBHist Q)
    (sternBrocotDecodeBHist R)
    (sternBrocotDecodeBHist H)
    (sternBrocotDecodeBHist C)
    (sternBrocotDecodeBHist P)
    (sternBrocotDecodeBHist N)

private def sternBrocotRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => sternBrocotRawAt n rest

private def sternBrocotLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => sternBrocotLengthEq n rest

def sternBrocotFromEventFlow (flow : EventFlow) : Option SternBrocotUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match sternBrocotLengthEq 12 flow with
  | true =>
      some
        (sternBrocotDecodePacket
          (sternBrocotRawAt 0 flow)
          (sternBrocotRawAt 1 flow)
          (sternBrocotRawAt 2 flow)
          (sternBrocotRawAt 3 flow)
          (sternBrocotRawAt 4 flow)
          (sternBrocotRawAt 5 flow)
          (sternBrocotRawAt 6 flow)
          (sternBrocotRawAt 7 flow)
          (sternBrocotRawAt 8 flow)
          (sternBrocotRawAt 9 flow)
          (sternBrocotRawAt 10 flow)
          (sternBrocotRawAt 11 flow))
  | false => none

private theorem SternBrocotUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SternBrocotUp,
      sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A L U M F B Q R H C P N =>
      change
        some
          (sternBrocotDecodePacket
            (sternBrocotEncodeBHist A)
            (sternBrocotEncodeBHist L)
            (sternBrocotEncodeBHist U)
            (sternBrocotEncodeBHist M)
            (sternBrocotEncodeBHist F)
            (sternBrocotEncodeBHist B)
            (sternBrocotEncodeBHist Q)
            (sternBrocotEncodeBHist R)
            (sternBrocotEncodeBHist H)
            (sternBrocotEncodeBHist C)
            (sternBrocotEncodeBHist P)
            (sternBrocotEncodeBHist N)) =
          some (SternBrocotUp.mk A L U M F B Q R H C P N)
      unfold sternBrocotDecodePacket
      rw [SternBrocotUpTasteGate_single_carrier_alignment_decode A,
        SternBrocotUpTasteGate_single_carrier_alignment_decode L,
        SternBrocotUpTasteGate_single_carrier_alignment_decode U,
        SternBrocotUpTasteGate_single_carrier_alignment_decode M,
        SternBrocotUpTasteGate_single_carrier_alignment_decode F,
        SternBrocotUpTasteGate_single_carrier_alignment_decode B,
        SternBrocotUpTasteGate_single_carrier_alignment_decode Q,
        SternBrocotUpTasteGate_single_carrier_alignment_decode R,
        SternBrocotUpTasteGate_single_carrier_alignment_decode H,
        SternBrocotUpTasteGate_single_carrier_alignment_decode C,
        SternBrocotUpTasteGate_single_carrier_alignment_decode P,
        SternBrocotUpTasteGate_single_carrier_alignment_decode N]

private theorem SternBrocotUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SternBrocotUp} :
    sternBrocotToEventFlow x = sternBrocotToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sternBrocotFromEventFlow (sternBrocotToEventFlow x) =
        sternBrocotFromEventFlow (sternBrocotToEventFlow y) :=
    congrArg sternBrocotFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SternBrocotUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SternBrocotUpTasteGate_single_carrier_alignment_round_trip y)))

instance sternBrocotBHistCarrier : BHistCarrier SternBrocotUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sternBrocotToEventFlow
  fromEventFlow := sternBrocotFromEventFlow

instance sternBrocotChapterTasteGate : ChapterTasteGate SternBrocotUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x
    exact SternBrocotUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SternBrocotUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SternBrocotUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, sternBrocotDecodeBHist (sternBrocotEncodeBHist h) = h) ∧
      (∀ x : SternBrocotUp,
        sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x) ∧
      (∀ x y : SternBrocotUp,
        sternBrocotToEventFlow x = sternBrocotToEventFlow y → x = y) ∧
      sternBrocotEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SternBrocotUpTasteGate_single_carrier_alignment_decode,
      SternBrocotUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SternBrocotUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SternBrocotUp
