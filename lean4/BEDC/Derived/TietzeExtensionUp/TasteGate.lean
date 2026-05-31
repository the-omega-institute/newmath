import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TietzeExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TietzeExtensionUp : Type where
  | mk (N D B U M G R H K P L : BHist) : TietzeExtensionUp
  deriving DecidableEq

def tietzeExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tietzeExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tietzeExtensionEncodeBHist h

def tietzeExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tietzeExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tietzeExtensionDecodeBHist tail)

private theorem TietzeExtensionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def tietzeExtensionFields : TietzeExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TietzeExtensionUp.mk N D B U M G R H K P L => [N, D, B, U, M, G, R, H, K, P, L]

def tietzeExtensionToEventFlow : TietzeExtensionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (tietzeExtensionFields x).map tietzeExtensionEncodeBHist

private def tietzeExtensionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => tietzeExtensionEventAtDefault index rest

def tietzeExtensionFromEventFlow : EventFlow → Option TietzeExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (TietzeExtensionUp.mk
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 0 ef))
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 1 ef))
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 2 ef))
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 3 ef))
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 4 ef))
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 5 ef))
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 6 ef))
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 7 ef))
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 8 ef))
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 9 ef))
        (tietzeExtensionDecodeBHist (tietzeExtensionEventAtDefault 10 ef)))

private theorem TietzeExtensionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TietzeExtensionUp,
      tietzeExtensionFromEventFlow (tietzeExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N D B U M G R H K P L =>
      change
        some
          (TietzeExtensionUp.mk
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist N))
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist D))
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist B))
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist U))
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist M))
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist G))
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist R))
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist H))
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist K))
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist P))
            (tietzeExtensionDecodeBHist (tietzeExtensionEncodeBHist L))) =
          some (TietzeExtensionUp.mk N D B U M G R H K P L)
      rw [TietzeExtensionTasteGate_single_carrier_alignment_decode N,
        TietzeExtensionTasteGate_single_carrier_alignment_decode D,
        TietzeExtensionTasteGate_single_carrier_alignment_decode B,
        TietzeExtensionTasteGate_single_carrier_alignment_decode U,
        TietzeExtensionTasteGate_single_carrier_alignment_decode M,
        TietzeExtensionTasteGate_single_carrier_alignment_decode G,
        TietzeExtensionTasteGate_single_carrier_alignment_decode R,
        TietzeExtensionTasteGate_single_carrier_alignment_decode H,
        TietzeExtensionTasteGate_single_carrier_alignment_decode K,
        TietzeExtensionTasteGate_single_carrier_alignment_decode P,
        TietzeExtensionTasteGate_single_carrier_alignment_decode L]

private theorem tietzeExtensionToEventFlow_injective {x y : TietzeExtensionUp} :
    tietzeExtensionToEventFlow x = tietzeExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tietzeExtensionFromEventFlow (tietzeExtensionToEventFlow x) =
        tietzeExtensionFromEventFlow (tietzeExtensionToEventFlow y) :=
    congrArg tietzeExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TietzeExtensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TietzeExtensionTasteGate_single_carrier_alignment_round_trip y)))

instance tietzeExtensionBHistCarrier : BHistCarrier TietzeExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tietzeExtensionToEventFlow
  fromEventFlow := tietzeExtensionFromEventFlow

instance tietzeExtensionChapterTasteGate : ChapterTasteGate TietzeExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tietzeExtensionFromEventFlow (tietzeExtensionToEventFlow x) = some x
    exact TietzeExtensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tietzeExtensionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate TietzeExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tietzeExtensionChapterTasteGate

theorem TietzeExtensionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier TietzeExtensionUp) ∧
      Nonempty (ChapterTasteGate TietzeExtensionUp) ∧
        ∀ x : TietzeExtensionUp,
          tietzeExtensionFromEventFlow (tietzeExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨tietzeExtensionBHistCarrier⟩, ⟨tietzeExtensionChapterTasteGate⟩,
      TietzeExtensionTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.TietzeExtensionUp
