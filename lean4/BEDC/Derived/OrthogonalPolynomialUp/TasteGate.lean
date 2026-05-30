import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OrthogonalPolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OrthogonalPolynomialUp : Type where
  | mk (F M R N Z E H C P A : BHist) : OrthogonalPolynomialUp
  deriving DecidableEq

def orthogonalPolynomialEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: orthogonalPolynomialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: orthogonalPolynomialEncodeBHist h

def orthogonalPolynomialDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (orthogonalPolynomialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (orthogonalPolynomialDecodeBHist tail)

private theorem OrthogonalPolynomialTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def orthogonalPolynomialFields : OrthogonalPolynomialUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OrthogonalPolynomialUp.mk F M R N Z E H C P A => [F, M, R, N, Z, E, H, C, P, A]

def orthogonalPolynomialToEventFlow : OrthogonalPolynomialUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (orthogonalPolynomialFields x).map orthogonalPolynomialEncodeBHist

private def orthogonalPolynomialEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => orthogonalPolynomialEventAtDefault index rest

def orthogonalPolynomialFromEventFlow : EventFlow → Option OrthogonalPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (OrthogonalPolynomialUp.mk
        (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEventAtDefault 0 ef))
        (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEventAtDefault 1 ef))
        (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEventAtDefault 2 ef))
        (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEventAtDefault 3 ef))
        (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEventAtDefault 4 ef))
        (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEventAtDefault 5 ef))
        (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEventAtDefault 6 ef))
        (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEventAtDefault 7 ef))
        (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEventAtDefault 8 ef))
        (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEventAtDefault 9 ef)))

private theorem OrthogonalPolynomialTasteGate_single_carrier_alignment_round_trip :
    ∀ x : OrthogonalPolynomialUp,
      orthogonalPolynomialFromEventFlow (orthogonalPolynomialToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F M R N Z E H C P A =>
      change
        some
          (OrthogonalPolynomialUp.mk
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist F))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist M))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist R))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist N))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist Z))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist E))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist H))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist C))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist P))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist A))) =
          some (OrthogonalPolynomialUp.mk F M R N Z E H C P A)
      rw [OrthogonalPolynomialTasteGate_single_carrier_alignment_decode F,
        OrthogonalPolynomialTasteGate_single_carrier_alignment_decode M,
        OrthogonalPolynomialTasteGate_single_carrier_alignment_decode R,
        OrthogonalPolynomialTasteGate_single_carrier_alignment_decode N,
        OrthogonalPolynomialTasteGate_single_carrier_alignment_decode Z,
        OrthogonalPolynomialTasteGate_single_carrier_alignment_decode E,
        OrthogonalPolynomialTasteGate_single_carrier_alignment_decode H,
        OrthogonalPolynomialTasteGate_single_carrier_alignment_decode C,
        OrthogonalPolynomialTasteGate_single_carrier_alignment_decode P,
        OrthogonalPolynomialTasteGate_single_carrier_alignment_decode A]

private theorem orthogonalPolynomialToEventFlow_injective {x y : OrthogonalPolynomialUp} :
    orthogonalPolynomialToEventFlow x = orthogonalPolynomialToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      orthogonalPolynomialFromEventFlow (orthogonalPolynomialToEventFlow x) =
        orthogonalPolynomialFromEventFlow (orthogonalPolynomialToEventFlow y) :=
    congrArg orthogonalPolynomialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OrthogonalPolynomialTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OrthogonalPolynomialTasteGate_single_carrier_alignment_round_trip y)))

private theorem OrthogonalPolynomialTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : OrthogonalPolynomialUp, orthogonalPolynomialFields x = orthogonalPolynomialFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ M₁ R₁ N₁ Z₁ E₁ H₁ C₁ P₁ A₁ =>
      cases y with
      | mk F₂ M₂ R₂ N₂ Z₂ E₂ H₂ C₂ P₂ A₂ =>
          injection hfields with hF tail0
          injection tail0 with hM tail1
          injection tail1 with hR tail2
          injection tail2 with hN tail3
          injection tail3 with hZ tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hA _
          subst hF
          subst hM
          subst hR
          subst hN
          subst hZ
          subst hE
          subst hH
          subst hC
          subst hP
          subst hA
          rfl

instance orthogonalPolynomialBHistCarrier : BHistCarrier OrthogonalPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := orthogonalPolynomialToEventFlow
  fromEventFlow := orthogonalPolynomialFromEventFlow

instance orthogonalPolynomialChapterTasteGate : ChapterTasteGate OrthogonalPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change orthogonalPolynomialFromEventFlow (orthogonalPolynomialToEventFlow x) = some x
    exact OrthogonalPolynomialTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (orthogonalPolynomialToEventFlow_injective heq)

instance orthogonalPolynomialFieldFaithful : FieldFaithful OrthogonalPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := orthogonalPolynomialFields
  field_faithful := OrthogonalPolynomialTasteGate_single_carrier_alignment_fields_faithful

instance orthogonalPolynomialNontrivial : Nontrivial OrthogonalPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OrthogonalPolynomialUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OrthogonalPolynomialUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OrthogonalPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  orthogonalPolynomialChapterTasteGate

theorem OrthogonalPolynomialTasteGate_single_carrier_alignment :
    (∀ h : BHist, orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist h) = h) ∧
      (∀ x : OrthogonalPolynomialUp,
        orthogonalPolynomialFromEventFlow (orthogonalPolynomialToEventFlow x) = some x) ∧
        (∀ x y : OrthogonalPolynomialUp,
          orthogonalPolynomialToEventFlow x = orthogonalPolynomialToEventFlow y → x = y) ∧
          orthogonalPolynomialEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨OrthogonalPolynomialTasteGate_single_carrier_alignment_decode,
      OrthogonalPolynomialTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => orthogonalPolynomialToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.OrthogonalPolynomialUp
