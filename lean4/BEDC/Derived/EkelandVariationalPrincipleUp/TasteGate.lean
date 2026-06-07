import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EkelandVariationalPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EkelandVariationalPrincipleUp : Type where
  | mk (X d M L R A T W H C P N : BHist) : EkelandVariationalPrincipleUp
  deriving DecidableEq

def ekelandVariationalPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ekelandVariationalPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ekelandVariationalPrincipleEncodeBHist h

def ekelandVariationalPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ekelandVariationalPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ekelandVariationalPrincipleDecodeBHist tail)

private theorem ekelandVariationalPrinciple_decode_encode_bhist :
    ∀ h : BHist,
      ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ekelandVariationalPrincipleFields :
    EkelandVariationalPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EkelandVariationalPrincipleUp.mk X d M L R A T W H C P N =>
      [X, d, M, L, R, A, T, W, H, C, P, N]

def ekelandVariationalPrincipleToEventFlow :
    EkelandVariationalPrincipleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (ekelandVariationalPrincipleFields x).map
      ekelandVariationalPrincipleEncodeBHist

private def ekelandVariationalPrincipleRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ekelandVariationalPrincipleRawAt index rest

def ekelandVariationalPrincipleFromEventFlow
    (flow : EventFlow) : Option EkelandVariationalPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EkelandVariationalPrincipleUp.mk
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 0 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 1 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 2 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 3 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 4 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 5 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 6 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 7 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 8 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 9 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 10 flow))
      (ekelandVariationalPrincipleDecodeBHist
        (ekelandVariationalPrincipleRawAt 11 flow)))

private theorem ekelandVariationalPrinciple_round_trip :
    ∀ x : EkelandVariationalPrincipleUp,
      ekelandVariationalPrincipleFromEventFlow
        (ekelandVariationalPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d M L R A T W H C P N =>
      change
        some
          (EkelandVariationalPrincipleUp.mk
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist X))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist d))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist M))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist L))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist R))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist A))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist T))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist W))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist H))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist C))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist P))
            (ekelandVariationalPrincipleDecodeBHist
              (ekelandVariationalPrincipleEncodeBHist N))) =
          some (EkelandVariationalPrincipleUp.mk X d M L R A T W H C P N)
      rw [ekelandVariationalPrinciple_decode_encode_bhist X,
        ekelandVariationalPrinciple_decode_encode_bhist d,
        ekelandVariationalPrinciple_decode_encode_bhist M,
        ekelandVariationalPrinciple_decode_encode_bhist L,
        ekelandVariationalPrinciple_decode_encode_bhist R,
        ekelandVariationalPrinciple_decode_encode_bhist A,
        ekelandVariationalPrinciple_decode_encode_bhist T,
        ekelandVariationalPrinciple_decode_encode_bhist W,
        ekelandVariationalPrinciple_decode_encode_bhist H,
        ekelandVariationalPrinciple_decode_encode_bhist C,
        ekelandVariationalPrinciple_decode_encode_bhist P,
        ekelandVariationalPrinciple_decode_encode_bhist N]

private theorem ekelandVariationalPrincipleToEventFlow_injective
    {x y : EkelandVariationalPrincipleUp} :
    ekelandVariationalPrincipleToEventFlow x =
      ekelandVariationalPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ekelandVariationalPrincipleFromEventFlow
          (ekelandVariationalPrincipleToEventFlow x) =
        ekelandVariationalPrincipleFromEventFlow
          (ekelandVariationalPrincipleToEventFlow y) :=
    congrArg ekelandVariationalPrincipleFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (ekelandVariationalPrinciple_round_trip x).symm
        (Eq.trans hread (ekelandVariationalPrinciple_round_trip y)))

private theorem ekelandVariationalPrinciple_field_faithful :
    ∀ x y : EkelandVariationalPrincipleUp,
      ekelandVariationalPrincipleFields x =
        ekelandVariationalPrincipleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance ekelandVariationalPrincipleBHistCarrier :
    BHistCarrier EkelandVariationalPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ekelandVariationalPrincipleToEventFlow
  fromEventFlow := ekelandVariationalPrincipleFromEventFlow

instance ekelandVariationalPrincipleChapterTasteGate :
    ChapterTasteGate EkelandVariationalPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ekelandVariationalPrincipleFromEventFlow
        (ekelandVariationalPrincipleToEventFlow x) = some x
    exact ekelandVariationalPrinciple_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ekelandVariationalPrincipleToEventFlow_injective heq)

instance ekelandVariationalPrincipleFieldFaithful :
    FieldFaithful EkelandVariationalPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ekelandVariationalPrincipleFields
  field_faithful := ekelandVariationalPrinciple_field_faithful

instance ekelandVariationalPrincipleNontrivial :
    BEDC.Meta.TasteGate.Nontrivial EkelandVariationalPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EkelandVariationalPrincipleUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EkelandVariationalPrincipleUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EkelandVariationalPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ekelandVariationalPrincipleChapterTasteGate

theorem EkelandVariationalPrincipleTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier EkelandVariationalPrincipleUp) ∧
      Nonempty (ChapterTasteGate EkelandVariationalPrincipleUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial EkelandVariationalPrincipleUp) ∧
      (∀ h : BHist,
        ekelandVariationalPrincipleDecodeBHist
          (ekelandVariationalPrincipleEncodeBHist h) = h) ∧
      (∀ x : EkelandVariationalPrincipleUp,
        ekelandVariationalPrincipleFromEventFlow
          (ekelandVariationalPrincipleToEventFlow x) = some x) ∧
      (∀ x y : EkelandVariationalPrincipleUp,
        ekelandVariationalPrincipleToEventFlow x =
          ekelandVariationalPrincipleToEventFlow y → x = y) ∧
      ekelandVariationalPrincipleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨ekelandVariationalPrincipleBHistCarrier⟩,
      ⟨ekelandVariationalPrincipleChapterTasteGate⟩,
      ⟨ekelandVariationalPrincipleNontrivial⟩,
      ekelandVariationalPrinciple_decode_encode_bhist,
      ekelandVariationalPrinciple_round_trip,
      (fun _ _ heq => ekelandVariationalPrincipleToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EkelandVariationalPrincipleUp
