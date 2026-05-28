import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterSubbasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterSubbasisUp : Type where
  | mk (U I E G B F W T R L H C P N : BHist) : CauchyFilterSubbasisUp
  deriving DecidableEq

def cauchyFilterSubbasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterSubbasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterSubbasisEncodeBHist h

def cauchyFilterSubbasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterSubbasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterSubbasisDecodeBHist tail)

private theorem cauchyFilterSubbasis_decode_encode :
    ∀ h : BHist, cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterSubbasisFields : CauchyFilterSubbasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterSubbasisUp.mk U I E G B F W T R L H C P N =>
      [U, I, E, G, B, F, W, T, R, L, H, C, P, N]

def cauchyFilterSubbasisToEventFlow : CauchyFilterSubbasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyFilterSubbasisFields x).map cauchyFilterSubbasisEncodeBHist

private def cauchyFilterSubbasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyFilterSubbasisEventAtDefault index rest

def cauchyFilterSubbasisFromEventFlow : EventFlow → Option CauchyFilterSubbasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyFilterSubbasisUp.mk
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 0 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 1 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 2 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 3 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 4 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 5 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 6 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 7 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 8 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 9 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 10 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 11 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 12 ef))
        (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEventAtDefault 13 ef)))

private theorem cauchyFilterSubbasis_round_trip :
    ∀ x : CauchyFilterSubbasisUp,
      cauchyFilterSubbasisFromEventFlow (cauchyFilterSubbasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U I E G B F W T R L H C P N =>
      change
        some
          (CauchyFilterSubbasisUp.mk
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist U))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist I))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist E))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist G))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist B))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist F))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist W))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist T))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist R))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist L))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist H))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist C))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist P))
            (cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist N))) =
          some (CauchyFilterSubbasisUp.mk U I E G B F W T R L H C P N)
      rw [cauchyFilterSubbasis_decode_encode U, cauchyFilterSubbasis_decode_encode I,
        cauchyFilterSubbasis_decode_encode E, cauchyFilterSubbasis_decode_encode G,
        cauchyFilterSubbasis_decode_encode B, cauchyFilterSubbasis_decode_encode F,
        cauchyFilterSubbasis_decode_encode W, cauchyFilterSubbasis_decode_encode T,
        cauchyFilterSubbasis_decode_encode R, cauchyFilterSubbasis_decode_encode L,
        cauchyFilterSubbasis_decode_encode H, cauchyFilterSubbasis_decode_encode C,
        cauchyFilterSubbasis_decode_encode P, cauchyFilterSubbasis_decode_encode N]

private theorem cauchyFilterSubbasisToEventFlow_injective {x y : CauchyFilterSubbasisUp} :
    cauchyFilterSubbasisToEventFlow x = cauchyFilterSubbasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterSubbasisFromEventFlow (cauchyFilterSubbasisToEventFlow x) =
        cauchyFilterSubbasisFromEventFlow (cauchyFilterSubbasisToEventFlow y) :=
    congrArg cauchyFilterSubbasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyFilterSubbasis_round_trip x).symm
      (Eq.trans hread (cauchyFilterSubbasis_round_trip y)))

private theorem cauchyFilterSubbasis_field_faithful :
    ∀ x y : CauchyFilterSubbasisUp,
      cauchyFilterSubbasisFields x = cauchyFilterSubbasisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ I₁ E₁ G₁ B₁ F₁ W₁ T₁ R₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ I₂ E₂ G₂ B₂ F₂ W₂ T₂ R₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyFilterSubbasisBHistCarrier : BHistCarrier CauchyFilterSubbasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterSubbasisToEventFlow
  fromEventFlow := cauchyFilterSubbasisFromEventFlow

instance cauchyFilterSubbasisChapterTasteGate : ChapterTasteGate CauchyFilterSubbasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterSubbasisFromEventFlow (cauchyFilterSubbasisToEventFlow x) = some x
    exact cauchyFilterSubbasis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyFilterSubbasisToEventFlow_injective heq)

instance cauchyFilterSubbasisFieldFaithful : FieldFaithful CauchyFilterSubbasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyFilterSubbasisFields
  field_faithful := cauchyFilterSubbasis_field_faithful

def taste_gate : ChapterTasteGate CauchyFilterSubbasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterSubbasisChapterTasteGate

theorem CauchyFilterSubbasisTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyFilterSubbasisDecodeBHist (cauchyFilterSubbasisEncodeBHist h) = h) ∧
      (∀ x : CauchyFilterSubbasisUp,
        cauchyFilterSubbasisFromEventFlow (cauchyFilterSubbasisToEventFlow x) = some x) ∧
      (∀ x y : CauchyFilterSubbasisUp,
        cauchyFilterSubbasisToEventFlow x = cauchyFilterSubbasisToEventFlow y → x = y) ∧
      Nonempty (FieldFaithful CauchyFilterSubbasisUp) ∧
      cauchyFilterSubbasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨cauchyFilterSubbasis_decode_encode,
      cauchyFilterSubbasis_round_trip,
      (fun _ _ heq => cauchyFilterSubbasisToEventFlow_injective heq),
      ⟨cauchyFilterSubbasisFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.CauchyFilterSubbasisUp
