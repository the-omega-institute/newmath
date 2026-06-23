import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedNormalEqualityFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedNormalEqualityFrontierUp : Type where
  | mk (I F L N E R H C P A : BHist) : BoundedNormalEqualityFrontierUp
  deriving DecidableEq

def boundedNormalEqualityFrontierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedNormalEqualityFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedNormalEqualityFrontierEncodeBHist h

def boundedNormalEqualityFrontierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedNormalEqualityFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedNormalEqualityFrontierDecodeBHist tail)

private theorem boundedNormalEqualityFrontierDecode_encode :
    ∀ h : BHist,
      boundedNormalEqualityFrontierDecodeBHist
        (boundedNormalEqualityFrontierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedNormalEqualityFrontierFields :
    BoundedNormalEqualityFrontierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedNormalEqualityFrontierUp.mk I F L N E R H C P A =>
      [I, F, L, N, E, R, H, C, P, A]

def boundedNormalEqualityFrontierToEventFlow :
    BoundedNormalEqualityFrontierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (boundedNormalEqualityFrontierFields x).map
        boundedNormalEqualityFrontierEncodeBHist

private def boundedNormalEqualityFrontierEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      boundedNormalEqualityFrontierEventAtDefault index rest

def boundedNormalEqualityFrontierFromEventFlow :
    EventFlow → Option BoundedNormalEqualityFrontierUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BoundedNormalEqualityFrontierUp.mk
          (boundedNormalEqualityFrontierDecodeBHist
            (boundedNormalEqualityFrontierEventAtDefault 0 ef))
          (boundedNormalEqualityFrontierDecodeBHist
            (boundedNormalEqualityFrontierEventAtDefault 1 ef))
          (boundedNormalEqualityFrontierDecodeBHist
            (boundedNormalEqualityFrontierEventAtDefault 2 ef))
          (boundedNormalEqualityFrontierDecodeBHist
            (boundedNormalEqualityFrontierEventAtDefault 3 ef))
          (boundedNormalEqualityFrontierDecodeBHist
            (boundedNormalEqualityFrontierEventAtDefault 4 ef))
          (boundedNormalEqualityFrontierDecodeBHist
            (boundedNormalEqualityFrontierEventAtDefault 5 ef))
          (boundedNormalEqualityFrontierDecodeBHist
            (boundedNormalEqualityFrontierEventAtDefault 6 ef))
          (boundedNormalEqualityFrontierDecodeBHist
            (boundedNormalEqualityFrontierEventAtDefault 7 ef))
          (boundedNormalEqualityFrontierDecodeBHist
            (boundedNormalEqualityFrontierEventAtDefault 8 ef))
          (boundedNormalEqualityFrontierDecodeBHist
            (boundedNormalEqualityFrontierEventAtDefault 9 ef)))

private theorem boundedNormalEqualityFrontier_round_trip :
    ∀ x : BoundedNormalEqualityFrontierUp,
      boundedNormalEqualityFrontierFromEventFlow
        (boundedNormalEqualityFrontierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F L N E R H C P A =>
      change
        some
            (BoundedNormalEqualityFrontierUp.mk
              (boundedNormalEqualityFrontierDecodeBHist
                (boundedNormalEqualityFrontierEncodeBHist I))
              (boundedNormalEqualityFrontierDecodeBHist
                (boundedNormalEqualityFrontierEncodeBHist F))
              (boundedNormalEqualityFrontierDecodeBHist
                (boundedNormalEqualityFrontierEncodeBHist L))
              (boundedNormalEqualityFrontierDecodeBHist
                (boundedNormalEqualityFrontierEncodeBHist N))
              (boundedNormalEqualityFrontierDecodeBHist
                (boundedNormalEqualityFrontierEncodeBHist E))
              (boundedNormalEqualityFrontierDecodeBHist
                (boundedNormalEqualityFrontierEncodeBHist R))
              (boundedNormalEqualityFrontierDecodeBHist
                (boundedNormalEqualityFrontierEncodeBHist H))
              (boundedNormalEqualityFrontierDecodeBHist
                (boundedNormalEqualityFrontierEncodeBHist C))
              (boundedNormalEqualityFrontierDecodeBHist
                (boundedNormalEqualityFrontierEncodeBHist P))
              (boundedNormalEqualityFrontierDecodeBHist
                (boundedNormalEqualityFrontierEncodeBHist A))) =
          some (BoundedNormalEqualityFrontierUp.mk I F L N E R H C P A)
      rw [boundedNormalEqualityFrontierDecode_encode I,
        boundedNormalEqualityFrontierDecode_encode F,
        boundedNormalEqualityFrontierDecode_encode L,
        boundedNormalEqualityFrontierDecode_encode N,
        boundedNormalEqualityFrontierDecode_encode E,
        boundedNormalEqualityFrontierDecode_encode R,
        boundedNormalEqualityFrontierDecode_encode H,
        boundedNormalEqualityFrontierDecode_encode C,
        boundedNormalEqualityFrontierDecode_encode P,
        boundedNormalEqualityFrontierDecode_encode A]

private theorem boundedNormalEqualityFrontierToEventFlow_injective
    {x y : BoundedNormalEqualityFrontierUp} :
    boundedNormalEqualityFrontierToEventFlow x =
        boundedNormalEqualityFrontierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedNormalEqualityFrontierFromEventFlow
          (boundedNormalEqualityFrontierToEventFlow x) =
        boundedNormalEqualityFrontierFromEventFlow
          (boundedNormalEqualityFrontierToEventFlow y) :=
    congrArg boundedNormalEqualityFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (boundedNormalEqualityFrontier_round_trip x).symm
      (Eq.trans hread (boundedNormalEqualityFrontier_round_trip y)))

private theorem boundedNormalEqualityFrontier_fields_faithful :
    ∀ x y : BoundedNormalEqualityFrontierUp,
      boundedNormalEqualityFrontierFields x =
          boundedNormalEqualityFrontierFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ F₁ L₁ N₁ E₁ R₁ H₁ C₁ P₁ A₁ =>
      cases y with
      | mk I₂ F₂ L₂ N₂ E₂ R₂ H₂ C₂ P₂ A₂ =>
          injection hfields with hI tail0
          injection tail0 with hF tail1
          injection tail1 with hL tail2
          injection tail2 with hN tail3
          injection tail3 with hE tail4
          injection tail4 with hR tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hA _
          subst hI
          subst hF
          subst hL
          subst hN
          subst hE
          subst hR
          subst hH
          subst hC
          subst hP
          subst hA
          rfl

instance boundedNormalEqualityFrontierBHistCarrier :
    BHistCarrier BoundedNormalEqualityFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedNormalEqualityFrontierToEventFlow
  fromEventFlow := boundedNormalEqualityFrontierFromEventFlow

instance boundedNormalEqualityFrontierChapterTasteGate :
    ChapterTasteGate BoundedNormalEqualityFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedNormalEqualityFrontierFromEventFlow
          (boundedNormalEqualityFrontierToEventFlow x) =
        some x
    exact boundedNormalEqualityFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedNormalEqualityFrontierToEventFlow_injective heq)

instance boundedNormalEqualityFrontierFieldFaithful :
    FieldFaithful BoundedNormalEqualityFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedNormalEqualityFrontierFields
  field_faithful := boundedNormalEqualityFrontier_fields_faithful

instance boundedNormalEqualityFrontierNontrivial :
    Nontrivial BoundedNormalEqualityFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedNormalEqualityFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BoundedNormalEqualityFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedNormalEqualityFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedNormalEqualityFrontierChapterTasteGate

theorem BoundedNormalEqualityFrontierTasteGate_single_carrier_alignment :
    (∀ x : BoundedNormalEqualityFrontierUp,
      boundedNormalEqualityFrontierFromEventFlow
        (boundedNormalEqualityFrontierToEventFlow x) = some x) ∧
      (∀ x y : BoundedNormalEqualityFrontierUp,
        boundedNormalEqualityFrontierToEventFlow x =
            boundedNormalEqualityFrontierToEventFlow y →
          x = y) ∧
        (∀ (x : BoundedNormalEqualityFrontierUp) w m,
          List.Mem w (boundedNormalEqualityFrontierToEventFlow x) →
            List.Mem m w →
              m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact boundedNormalEqualityFrontier_round_trip
  · constructor
    · intro x y heq
      exact boundedNormalEqualityFrontierToEventFlow_injective heq
    · intro _x w m hw hm
      exact event_flow_conservativity hw hm

end BEDC.Derived.BoundedNormalEqualityFrontierUp
