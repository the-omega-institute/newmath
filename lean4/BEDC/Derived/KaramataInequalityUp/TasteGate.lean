import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KaramataInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KaramataInequalityUp : Type where
  | mk (F X Y M A J R Q H C P N : BHist) : KaramataInequalityUp
  deriving DecidableEq

def karamataInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: karamataInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: karamataInequalityEncodeBHist h

def karamataInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (karamataInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (karamataInequalityDecodeBHist tail)

private theorem KaramataInequalityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, karamataInequalityDecodeBHist (karamataInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def karamataInequalityFields : KaramataInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KaramataInequalityUp.mk F X Y M A J R Q H C P N => [F, X, Y, M, A, J, R, Q, H, C, P, N]

def karamataInequalityToEventFlow : KaramataInequalityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (karamataInequalityFields x).map karamataInequalityEncodeBHist

private def karamataInequalityRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => karamataInequalityRawAt index rest

def karamataInequalityFromEventFlow (flow : EventFlow) : Option KaramataInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KaramataInequalityUp.mk
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 0 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 1 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 2 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 3 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 4 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 5 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 6 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 7 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 8 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 9 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 10 flow))
      (karamataInequalityDecodeBHist (karamataInequalityRawAt 11 flow)))

private theorem KaramataInequalityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KaramataInequalityUp,
      karamataInequalityFromEventFlow (karamataInequalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk F X Y M A J R Q H C P N =>
      change
        some
          (KaramataInequalityUp.mk
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist F))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist X))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist Y))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist M))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist A))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist J))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist R))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist Q))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist H))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist C))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist P))
            (karamataInequalityDecodeBHist (karamataInequalityEncodeBHist N))) =
          some (KaramataInequalityUp.mk F X Y M A J R Q H C P N)
      rw [KaramataInequalityTasteGate_single_carrier_alignment_decode F,
        KaramataInequalityTasteGate_single_carrier_alignment_decode X,
        KaramataInequalityTasteGate_single_carrier_alignment_decode Y,
        KaramataInequalityTasteGate_single_carrier_alignment_decode M,
        KaramataInequalityTasteGate_single_carrier_alignment_decode A,
        KaramataInequalityTasteGate_single_carrier_alignment_decode J,
        KaramataInequalityTasteGate_single_carrier_alignment_decode R,
        KaramataInequalityTasteGate_single_carrier_alignment_decode Q,
        KaramataInequalityTasteGate_single_carrier_alignment_decode H,
        KaramataInequalityTasteGate_single_carrier_alignment_decode C,
        KaramataInequalityTasteGate_single_carrier_alignment_decode P,
        KaramataInequalityTasteGate_single_carrier_alignment_decode N]

private theorem karamataInequalityToEventFlow_injective {x y : KaramataInequalityUp} :
    karamataInequalityToEventFlow x = karamataInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      karamataInequalityFromEventFlow (karamataInequalityToEventFlow x) =
        karamataInequalityFromEventFlow (karamataInequalityToEventFlow y) :=
    congrArg karamataInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (KaramataInequalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KaramataInequalityTasteGate_single_carrier_alignment_round_trip y)))

instance karamataInequalityBHistCarrier : BHistCarrier KaramataInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := karamataInequalityToEventFlow
  fromEventFlow := karamataInequalityFromEventFlow

instance karamataInequalityChapterTasteGate : ChapterTasteGate KaramataInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change karamataInequalityFromEventFlow (karamataInequalityToEventFlow x) = some x
    exact KaramataInequalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (karamataInequalityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate KaramataInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  karamataInequalityChapterTasteGate

theorem KaramataInequalityTasteGate_single_carrier_alignment :
    (∀ h : BHist, karamataInequalityDecodeBHist (karamataInequalityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier KaramataInequalityUp) ∧
        Nonempty (ChapterTasteGate KaramataInequalityUp) ∧
          karamataInequalityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KaramataInequalityTasteGate_single_carrier_alignment_decode,
      ⟨karamataInequalityBHistCarrier⟩,
      ⟨karamataInequalityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.KaramataInequalityUp
