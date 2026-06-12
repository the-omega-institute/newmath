import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UnaryZeroSpineStandardIsoUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UnaryZeroSpineStandardIsoUp : Type where
  | mk (U A L F R H C P N : BHist) : UnaryZeroSpineStandardIsoUp
  deriving DecidableEq

def unaryZeroSpineStandardIsoEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: unaryZeroSpineStandardIsoEncodeBHist h
  | BHist.e1 h => BMark.b1 :: unaryZeroSpineStandardIsoEncodeBHist h

def unaryZeroSpineStandardIsoDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (unaryZeroSpineStandardIsoDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (unaryZeroSpineStandardIsoDecodeBHist tail)

private theorem unaryZeroSpineStandardIso_decode_encode_bhist :
    ∀ h : BHist,
      unaryZeroSpineStandardIsoDecodeBHist (unaryZeroSpineStandardIsoEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def unaryZeroSpineStandardIsoFields : UnaryZeroSpineStandardIsoUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UnaryZeroSpineStandardIsoUp.mk U A L F R H C P N => [U, A, L, F, R, H, C, P, N]

def unaryZeroSpineStandardIsoToEventFlow : UnaryZeroSpineStandardIsoUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (unaryZeroSpineStandardIsoFields x).map unaryZeroSpineStandardIsoEncodeBHist

private def unaryZeroSpineStandardIsoEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => unaryZeroSpineStandardIsoEventAtDefault index rest

def unaryZeroSpineStandardIsoFromEventFlow
    (ef : EventFlow) : Option UnaryZeroSpineStandardIsoUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UnaryZeroSpineStandardIsoUp.mk
      (unaryZeroSpineStandardIsoDecodeBHist (unaryZeroSpineStandardIsoEventAtDefault 0 ef))
      (unaryZeroSpineStandardIsoDecodeBHist (unaryZeroSpineStandardIsoEventAtDefault 1 ef))
      (unaryZeroSpineStandardIsoDecodeBHist (unaryZeroSpineStandardIsoEventAtDefault 2 ef))
      (unaryZeroSpineStandardIsoDecodeBHist (unaryZeroSpineStandardIsoEventAtDefault 3 ef))
      (unaryZeroSpineStandardIsoDecodeBHist (unaryZeroSpineStandardIsoEventAtDefault 4 ef))
      (unaryZeroSpineStandardIsoDecodeBHist (unaryZeroSpineStandardIsoEventAtDefault 5 ef))
      (unaryZeroSpineStandardIsoDecodeBHist (unaryZeroSpineStandardIsoEventAtDefault 6 ef))
      (unaryZeroSpineStandardIsoDecodeBHist (unaryZeroSpineStandardIsoEventAtDefault 7 ef))
      (unaryZeroSpineStandardIsoDecodeBHist (unaryZeroSpineStandardIsoEventAtDefault 8 ef)))

private theorem unaryZeroSpineStandardIso_round_trip :
    ∀ x : UnaryZeroSpineStandardIsoUp,
      unaryZeroSpineStandardIsoFromEventFlow (unaryZeroSpineStandardIsoToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U A L F R H C P N =>
      change
        some
          (UnaryZeroSpineStandardIsoUp.mk
            (unaryZeroSpineStandardIsoDecodeBHist
              (unaryZeroSpineStandardIsoEncodeBHist U))
            (unaryZeroSpineStandardIsoDecodeBHist
              (unaryZeroSpineStandardIsoEncodeBHist A))
            (unaryZeroSpineStandardIsoDecodeBHist
              (unaryZeroSpineStandardIsoEncodeBHist L))
            (unaryZeroSpineStandardIsoDecodeBHist
              (unaryZeroSpineStandardIsoEncodeBHist F))
            (unaryZeroSpineStandardIsoDecodeBHist
              (unaryZeroSpineStandardIsoEncodeBHist R))
            (unaryZeroSpineStandardIsoDecodeBHist
              (unaryZeroSpineStandardIsoEncodeBHist H))
            (unaryZeroSpineStandardIsoDecodeBHist
              (unaryZeroSpineStandardIsoEncodeBHist C))
            (unaryZeroSpineStandardIsoDecodeBHist
              (unaryZeroSpineStandardIsoEncodeBHist P))
            (unaryZeroSpineStandardIsoDecodeBHist
              (unaryZeroSpineStandardIsoEncodeBHist N))) =
          some (UnaryZeroSpineStandardIsoUp.mk U A L F R H C P N)
      rw [unaryZeroSpineStandardIso_decode_encode_bhist U,
        unaryZeroSpineStandardIso_decode_encode_bhist A,
        unaryZeroSpineStandardIso_decode_encode_bhist L,
        unaryZeroSpineStandardIso_decode_encode_bhist F,
        unaryZeroSpineStandardIso_decode_encode_bhist R,
        unaryZeroSpineStandardIso_decode_encode_bhist H,
        unaryZeroSpineStandardIso_decode_encode_bhist C,
        unaryZeroSpineStandardIso_decode_encode_bhist P,
        unaryZeroSpineStandardIso_decode_encode_bhist N]

private theorem unaryZeroSpineStandardIsoToEventFlow_injective
    {x y : UnaryZeroSpineStandardIsoUp} :
    unaryZeroSpineStandardIsoToEventFlow x = unaryZeroSpineStandardIsoToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      unaryZeroSpineStandardIsoFromEventFlow (unaryZeroSpineStandardIsoToEventFlow x) =
        unaryZeroSpineStandardIsoFromEventFlow (unaryZeroSpineStandardIsoToEventFlow y) :=
    congrArg unaryZeroSpineStandardIsoFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (unaryZeroSpineStandardIso_round_trip x).symm
      (Eq.trans hread (unaryZeroSpineStandardIso_round_trip y)))

private theorem unaryZeroSpineStandardIso_field_faithful :
    ∀ x y : UnaryZeroSpineStandardIsoUp,
      unaryZeroSpineStandardIsoFields x = unaryZeroSpineStandardIsoFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ A₁ L₁ F₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ A₂ L₂ F₂ R₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hU tail0
          injection tail0 with hA tail1
          injection tail1 with hL tail2
          injection tail2 with hF tail3
          injection tail3 with hR tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hU
          subst hA
          subst hL
          subst hF
          subst hR
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance unaryZeroSpineStandardIsoBHistCarrier :
    BHistCarrier UnaryZeroSpineStandardIsoUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := unaryZeroSpineStandardIsoToEventFlow
  fromEventFlow := unaryZeroSpineStandardIsoFromEventFlow

instance unaryZeroSpineStandardIsoChapterTasteGate :
    ChapterTasteGate UnaryZeroSpineStandardIsoUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      unaryZeroSpineStandardIsoFromEventFlow (unaryZeroSpineStandardIsoToEventFlow x) =
        some x
    exact unaryZeroSpineStandardIso_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (unaryZeroSpineStandardIsoToEventFlow_injective heq)

instance unaryZeroSpineStandardIsoFieldFaithful :
    FieldFaithful UnaryZeroSpineStandardIsoUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := unaryZeroSpineStandardIsoFields
  field_faithful := unaryZeroSpineStandardIso_field_faithful

instance unaryZeroSpineStandardIsoNontrivial :
    BEDC.Meta.TasteGate.Nontrivial UnaryZeroSpineStandardIsoUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UnaryZeroSpineStandardIsoUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UnaryZeroSpineStandardIsoUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UnaryZeroSpineStandardIsoUp :=
  -- BEDC touchpoint anchor: BHist BMark
  unaryZeroSpineStandardIsoChapterTasteGate

theorem UnaryZeroSpineStandardIsoTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UnaryZeroSpineStandardIsoUp) ∧
      Nonempty (FieldFaithful UnaryZeroSpineStandardIsoUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial UnaryZeroSpineStandardIsoUp) ∧
          (∀ h : BHist,
            unaryZeroSpineStandardIsoDecodeBHist
              (unaryZeroSpineStandardIsoEncodeBHist h) = h) ∧
            (∀ x : UnaryZeroSpineStandardIsoUp,
              unaryZeroSpineStandardIsoFromEventFlow
                (unaryZeroSpineStandardIsoToEventFlow x) = some x) ∧
              (∀ x y : UnaryZeroSpineStandardIsoUp,
                unaryZeroSpineStandardIsoToEventFlow x =
                    unaryZeroSpineStandardIsoToEventFlow y ->
                  x = y) ∧
                unaryZeroSpineStandardIsoEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨unaryZeroSpineStandardIsoChapterTasteGate⟩,
      ⟨unaryZeroSpineStandardIsoFieldFaithful⟩,
      ⟨unaryZeroSpineStandardIsoNontrivial⟩,
      unaryZeroSpineStandardIso_decode_encode_bhist,
      unaryZeroSpineStandardIso_round_trip,
      (fun _ _ heq => unaryZeroSpineStandardIsoToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UnaryZeroSpineStandardIsoUp
