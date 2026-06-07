import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KirszbraunExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KirszbraunExtensionUp : Type where
  | mk (X A L Y V B F R H C P N : BHist) : KirszbraunExtensionUp
  deriving DecidableEq

def kirszbraunExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kirszbraunExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kirszbraunExtensionEncodeBHist h

def kirszbraunExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kirszbraunExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kirszbraunExtensionDecodeBHist tail)

private theorem KirszbraunExtensionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kirszbraunExtensionFields : KirszbraunExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KirszbraunExtensionUp.mk X A L Y V B F R H C P N => [X, A, L, Y, V, B, F, R, H, C, P, N]

def kirszbraunExtensionToEventFlow : KirszbraunExtensionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (kirszbraunExtensionFields x).map kirszbraunExtensionEncodeBHist

private def kirszbraunExtensionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kirszbraunExtensionEventAtDefault index rest

def kirszbraunExtensionFromEventFlow : EventFlow → Option KirszbraunExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (KirszbraunExtensionUp.mk
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 0 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 1 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 2 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 3 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 4 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 5 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 6 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 7 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 8 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 9 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 10 ef))
        (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEventAtDefault 11 ef)))

private theorem KirszbraunExtensionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KirszbraunExtensionUp,
      kirszbraunExtensionFromEventFlow (kirszbraunExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A L Y V B F R H C P N =>
      change
        some
          (KirszbraunExtensionUp.mk
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist X))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist A))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist L))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist Y))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist V))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist B))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist F))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist R))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist H))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist C))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist P))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist N))) =
          some (KirszbraunExtensionUp.mk X A L Y V B F R H C P N)
      rw [KirszbraunExtensionTasteGate_single_carrier_alignment_decode X,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode A,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode L,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode Y,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode V,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode B,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode F,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode R,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode H,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode C,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode P,
        KirszbraunExtensionTasteGate_single_carrier_alignment_decode N]

private theorem kirszbraunExtensionToEventFlow_injective {x y : KirszbraunExtensionUp} :
    kirszbraunExtensionToEventFlow x = kirszbraunExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kirszbraunExtensionFromEventFlow (kirszbraunExtensionToEventFlow x) =
        kirszbraunExtensionFromEventFlow (kirszbraunExtensionToEventFlow y) :=
    congrArg kirszbraunExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KirszbraunExtensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KirszbraunExtensionTasteGate_single_carrier_alignment_round_trip y)))

instance kirszbraunExtensionBHistCarrier : BHistCarrier KirszbraunExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kirszbraunExtensionToEventFlow
  fromEventFlow := kirszbraunExtensionFromEventFlow

instance kirszbraunExtensionChapterTasteGate : ChapterTasteGate KirszbraunExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kirszbraunExtensionFromEventFlow (kirszbraunExtensionToEventFlow x) = some x
    exact KirszbraunExtensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kirszbraunExtensionToEventFlow_injective heq)

theorem KirszbraunExtensionTasteGate_single_carrier_alignment :
    (∀ h : BHist, kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier KirszbraunExtensionUp) ∧
        Nonempty (ChapterTasteGate KirszbraunExtensionUp) ∧
          kirszbraunExtensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KirszbraunExtensionTasteGate_single_carrier_alignment_decode,
      ⟨kirszbraunExtensionBHistCarrier⟩, ⟨kirszbraunExtensionChapterTasteGate⟩, rfl⟩

end BEDC.Derived.KirszbraunExtensionUp
