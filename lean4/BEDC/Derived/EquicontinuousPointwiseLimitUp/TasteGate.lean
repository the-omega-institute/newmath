import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuousPointwiseLimitUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuousPointwiseLimitUp : Type where
  | mk (K F M W R A H C P N : BHist) : EquicontinuousPointwiseLimitUp
  deriving DecidableEq

def equicontinuousPointwiseLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: equicontinuousPointwiseLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: equicontinuousPointwiseLimitEncodeBHist h

def equicontinuousPointwiseLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (equicontinuousPointwiseLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (equicontinuousPointwiseLimitDecodeBHist tail)

private theorem equicontinuousPointwiseLimitDecode_encode_bhist :
    ∀ h : BHist,
      equicontinuousPointwiseLimitDecodeBHist
        (equicontinuousPointwiseLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def equicontinuousPointwiseLimitToEventFlow : EquicontinuousPointwiseLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuousPointwiseLimitUp.mk K F M W R A H C P N =>
      [equicontinuousPointwiseLimitEncodeBHist K,
        equicontinuousPointwiseLimitEncodeBHist F,
        equicontinuousPointwiseLimitEncodeBHist M,
        equicontinuousPointwiseLimitEncodeBHist W,
        equicontinuousPointwiseLimitEncodeBHist R,
        equicontinuousPointwiseLimitEncodeBHist A,
        equicontinuousPointwiseLimitEncodeBHist H,
        equicontinuousPointwiseLimitEncodeBHist C,
        equicontinuousPointwiseLimitEncodeBHist P,
        equicontinuousPointwiseLimitEncodeBHist N]

def equicontinuousPointwiseLimitFromEventFlow :
    EventFlow → Option EquicontinuousPointwiseLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [K, F, M, W, R, A, H, C, P, N] =>
      some (EquicontinuousPointwiseLimitUp.mk
        (equicontinuousPointwiseLimitDecodeBHist K)
        (equicontinuousPointwiseLimitDecodeBHist F)
        (equicontinuousPointwiseLimitDecodeBHist M)
        (equicontinuousPointwiseLimitDecodeBHist W)
        (equicontinuousPointwiseLimitDecodeBHist R)
        (equicontinuousPointwiseLimitDecodeBHist A)
        (equicontinuousPointwiseLimitDecodeBHist H)
        (equicontinuousPointwiseLimitDecodeBHist C)
        (equicontinuousPointwiseLimitDecodeBHist P)
        (equicontinuousPointwiseLimitDecodeBHist N))
  | _ => none

private theorem equicontinuousPointwiseLimit_round_trip :
    ∀ x : EquicontinuousPointwiseLimitUp,
      equicontinuousPointwiseLimitFromEventFlow
        (equicontinuousPointwiseLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F M W R A H C P N =>
      change
        some (EquicontinuousPointwiseLimitUp.mk
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitEncodeBHist K))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitEncodeBHist F))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitEncodeBHist M))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitEncodeBHist W))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitEncodeBHist R))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitEncodeBHist A))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitEncodeBHist H))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitEncodeBHist C))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitEncodeBHist P))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitEncodeBHist N))) =
          some (EquicontinuousPointwiseLimitUp.mk K F M W R A H C P N)
      rw [equicontinuousPointwiseLimitDecode_encode_bhist K,
        equicontinuousPointwiseLimitDecode_encode_bhist F,
        equicontinuousPointwiseLimitDecode_encode_bhist M,
        equicontinuousPointwiseLimitDecode_encode_bhist W,
        equicontinuousPointwiseLimitDecode_encode_bhist R,
        equicontinuousPointwiseLimitDecode_encode_bhist A,
        equicontinuousPointwiseLimitDecode_encode_bhist H,
        equicontinuousPointwiseLimitDecode_encode_bhist C,
        equicontinuousPointwiseLimitDecode_encode_bhist P,
        equicontinuousPointwiseLimitDecode_encode_bhist N]

private theorem equicontinuousPointwiseLimitToEventFlow_injective
    {x y : EquicontinuousPointwiseLimitUp} :
    equicontinuousPointwiseLimitToEventFlow x =
      equicontinuousPointwiseLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      equicontinuousPointwiseLimitFromEventFlow
          (equicontinuousPointwiseLimitToEventFlow x) =
        equicontinuousPointwiseLimitFromEventFlow
          (equicontinuousPointwiseLimitToEventFlow y) :=
    congrArg equicontinuousPointwiseLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (equicontinuousPointwiseLimit_round_trip x).symm
      (Eq.trans hread (equicontinuousPointwiseLimit_round_trip y)))

instance equicontinuousPointwiseLimitBHistCarrier :
    BHistCarrier EquicontinuousPointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := equicontinuousPointwiseLimitToEventFlow
  fromEventFlow := equicontinuousPointwiseLimitFromEventFlow

instance equicontinuousPointwiseLimitChapterTasteGate :
    ChapterTasteGate EquicontinuousPointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      equicontinuousPointwiseLimitFromEventFlow
        (equicontinuousPointwiseLimitToEventFlow x) = some x
    exact equicontinuousPointwiseLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (equicontinuousPointwiseLimitToEventFlow_injective heq)

instance equicontinuousPointwiseLimitFieldFaithful :
    FieldFaithful EquicontinuousPointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | EquicontinuousPointwiseLimitUp.mk K F M W R A H C P N =>
        [K, F, M, W, R, A, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk K₁ F₁ M₁ W₁ R₁ A₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk K₂ F₂ M₂ W₂ R₂ A₂ H₂ C₂ P₂ N₂ =>
            cases h
            rfl

instance equicontinuousPointwiseLimitNontrivial :
    Nontrivial EquicontinuousPointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EquicontinuousPointwiseLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EquicontinuousPointwiseLimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EquicontinuousPointwiseLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  equicontinuousPointwiseLimitChapterTasteGate

theorem EquicontinuousPointwiseLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, equicontinuousPointwiseLimitDecodeBHist
      (equicontinuousPointwiseLimitEncodeBHist h) = h) ∧
      (∀ x : EquicontinuousPointwiseLimitUp, equicontinuousPointwiseLimitFromEventFlow
        (equicontinuousPointwiseLimitToEventFlow x) = some x) ∧
        (∀ x y : EquicontinuousPointwiseLimitUp,
          equicontinuousPointwiseLimitToEventFlow x =
            equicontinuousPointwiseLimitToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate EquicontinuousPointwiseLimitUp) ∧
            Nonempty (FieldFaithful EquicontinuousPointwiseLimitUp) ∧
              Nonempty (Nontrivial EquicontinuousPointwiseLimitUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact equicontinuousPointwiseLimitDecode_encode_bhist
  · constructor
    · exact equicontinuousPointwiseLimit_round_trip
    · constructor
      · intro x y heq
        exact equicontinuousPointwiseLimitToEventFlow_injective heq
      · exact
          ⟨⟨equicontinuousPointwiseLimitChapterTasteGate⟩,
            ⟨equicontinuousPointwiseLimitFieldFaithful⟩,
            ⟨equicontinuousPointwiseLimitNontrivial⟩⟩

end BEDC.Derived.EquicontinuousPointwiseLimitUp.TasteGate

namespace BEDC.Derived.EquicontinuousPointwiseLimitUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.EquicontinuousPointwiseLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.EquicontinuousPointwiseLimitUp
