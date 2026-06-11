import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProductUniformSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProductUniformSpaceUp : Type where
  | mk (A B Pi EA EB W H C P N : BHist) : ProductUniformSpaceUp
  deriving DecidableEq

def productUniformSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: productUniformSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: productUniformSpaceEncodeBHist h

def productUniformSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (productUniformSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (productUniformSpaceDecodeBHist tail)

private theorem productUniformSpaceDecode_encode_bhist :
    ∀ h : BHist, productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def productUniformSpaceFields : ProductUniformSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProductUniformSpaceUp.mk A B Pi EA EB W H C P N => [A, B, Pi, EA, EB, W, H, C, P, N]

def productUniformSpaceToEventFlow : ProductUniformSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (productUniformSpaceFields x).map productUniformSpaceEncodeBHist

private def productUniformSpaceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => productUniformSpaceRawAt index rest

private def productUniformSpaceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => productUniformSpaceLengthEq index rest

def productUniformSpaceFromEventFlow : EventFlow → Option ProductUniformSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match productUniformSpaceLengthEq 10 flow with
      | true =>
          some
            (ProductUniformSpaceUp.mk
              (productUniformSpaceDecodeBHist (productUniformSpaceRawAt 0 flow))
              (productUniformSpaceDecodeBHist (productUniformSpaceRawAt 1 flow))
              (productUniformSpaceDecodeBHist (productUniformSpaceRawAt 2 flow))
              (productUniformSpaceDecodeBHist (productUniformSpaceRawAt 3 flow))
              (productUniformSpaceDecodeBHist (productUniformSpaceRawAt 4 flow))
              (productUniformSpaceDecodeBHist (productUniformSpaceRawAt 5 flow))
              (productUniformSpaceDecodeBHist (productUniformSpaceRawAt 6 flow))
              (productUniformSpaceDecodeBHist (productUniformSpaceRawAt 7 flow))
              (productUniformSpaceDecodeBHist (productUniformSpaceRawAt 8 flow))
              (productUniformSpaceDecodeBHist (productUniformSpaceRawAt 9 flow)))
      | false => none

private theorem productUniformSpace_round_trip :
    ∀ x : ProductUniformSpaceUp,
      productUniformSpaceFromEventFlow (productUniformSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B Pi EA EB W H C P N =>
      change
        some
          (ProductUniformSpaceUp.mk
            (productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist A))
            (productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist B))
            (productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist Pi))
            (productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist EA))
            (productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist EB))
            (productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist W))
            (productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist H))
            (productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist C))
            (productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist P))
            (productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist N))) =
          some (ProductUniformSpaceUp.mk A B Pi EA EB W H C P N)
      rw [productUniformSpaceDecode_encode_bhist A,
        productUniformSpaceDecode_encode_bhist B,
        productUniformSpaceDecode_encode_bhist Pi,
        productUniformSpaceDecode_encode_bhist EA,
        productUniformSpaceDecode_encode_bhist EB,
        productUniformSpaceDecode_encode_bhist W,
        productUniformSpaceDecode_encode_bhist H,
        productUniformSpaceDecode_encode_bhist C,
        productUniformSpaceDecode_encode_bhist P,
        productUniformSpaceDecode_encode_bhist N]

private theorem productUniformSpaceToEventFlow_injective {x y : ProductUniformSpaceUp} :
    productUniformSpaceToEventFlow x = productUniformSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      productUniformSpaceFromEventFlow (productUniformSpaceToEventFlow x) =
        productUniformSpaceFromEventFlow (productUniformSpaceToEventFlow y) :=
    congrArg productUniformSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (productUniformSpace_round_trip x).symm
      (Eq.trans hread (productUniformSpace_round_trip y)))

instance productUniformSpaceBHistCarrier : BHistCarrier ProductUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := productUniformSpaceToEventFlow
  fromEventFlow := productUniformSpaceFromEventFlow

instance productUniformSpaceChapterTasteGate :
    ChapterTasteGate ProductUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change productUniformSpaceFromEventFlow (productUniformSpaceToEventFlow x) = some x
    exact productUniformSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (productUniformSpaceToEventFlow_injective heq)

instance productUniformSpaceFieldFaithful : FieldFaithful ProductUniformSpaceUp where
  fields := productUniformSpaceFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk A₁ B₁ Pi₁ EA₁ EB₁ W₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk A₂ B₂ Pi₂ EA₂ EB₂ W₂ H₂ C₂ P₂ N₂ =>
            injection h with hA hTail₁
            injection hTail₁ with hB hTail₂
            injection hTail₂ with hPi hTail₃
            injection hTail₃ with hEA hTail₄
            injection hTail₄ with hEB hTail₅
            injection hTail₅ with hW hTail₆
            injection hTail₆ with hH hTail₇
            injection hTail₇ with hC hTail₈
            injection hTail₈ with hP hTail₉
            injection hTail₉ with hN _
            subst hA
            subst hB
            subst hPi
            subst hEA
            subst hEB
            subst hW
            subst hH
            subst hC
            subst hP
            subst hN
            rfl

instance productUniformSpaceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ProductUniformSpaceUp where
  witness_pair :=
    ⟨ProductUniformSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ProductUniformSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        injection h with hA _rest
        cases hA⟩

def taste_gate : ChapterTasteGate ProductUniformSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  productUniformSpaceChapterTasteGate

theorem ProductUniformSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ProductUniformSpaceUp) ∧
      Nonempty (FieldFaithful ProductUniformSpaceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ProductUniformSpaceUp) ∧
          (∀ h : BHist,
            productUniformSpaceDecodeBHist (productUniformSpaceEncodeBHist h) = h) ∧
            (∀ x : ProductUniformSpaceUp,
              productUniformSpaceFromEventFlow (productUniformSpaceToEventFlow x) =
                some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨Nonempty.intro productUniformSpaceChapterTasteGate,
      Nonempty.intro productUniformSpaceFieldFaithful,
      Nonempty.intro productUniformSpaceNontrivial,
      productUniformSpaceDecode_encode_bhist,
      productUniformSpace_round_trip⟩

end BEDC.Derived.ProductUniformSpaceUp
