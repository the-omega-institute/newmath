import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EilenbergMooreCompletionAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EilenbergMooreCompletionAlgebraUp : Type where
  | mk (M U K I L H C P N : BHist) : EilenbergMooreCompletionAlgebraUp
  deriving DecidableEq

def eilenbergMooreCompletionAlgebraEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eilenbergMooreCompletionAlgebraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eilenbergMooreCompletionAlgebraEncodeBHist h

def eilenbergMooreCompletionAlgebraDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eilenbergMooreCompletionAlgebraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eilenbergMooreCompletionAlgebraDecodeBHist tail)

private theorem EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      eilenbergMooreCompletionAlgebraDecodeBHist
        (eilenbergMooreCompletionAlgebraEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eilenbergMooreCompletionAlgebraFields :
    EilenbergMooreCompletionAlgebraUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EilenbergMooreCompletionAlgebraUp.mk M U K I L H C P N => [M, U, K, I, L, H, C, P, N]

def eilenbergMooreCompletionAlgebraToEventFlow :
    EilenbergMooreCompletionAlgebraUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EilenbergMooreCompletionAlgebraUp.mk M U K I L H C P N =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
        eilenbergMooreCompletionAlgebraEncodeBHist M,
        eilenbergMooreCompletionAlgebraEncodeBHist U,
        eilenbergMooreCompletionAlgebraEncodeBHist K,
        eilenbergMooreCompletionAlgebraEncodeBHist I,
        eilenbergMooreCompletionAlgebraEncodeBHist L,
        eilenbergMooreCompletionAlgebraEncodeBHist H,
        eilenbergMooreCompletionAlgebraEncodeBHist C,
        eilenbergMooreCompletionAlgebraEncodeBHist P,
        eilenbergMooreCompletionAlgebraEncodeBHist N]

def eilenbergMooreCompletionAlgebraFromEventFlow :
    EventFlow → Option EilenbergMooreCompletionAlgebraUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restM =>
      match restM with
      | [] => none
      | M :: restU =>
          match restU with
          | [] => none
          | U :: restK =>
              match restK with
              | [] => none
              | K :: restI =>
                  match restI with
                  | [] => none
                  | I :: restL =>
                      match restL with
                      | [] => none
                      | L :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (EilenbergMooreCompletionAlgebraUp.mk
                                                  (eilenbergMooreCompletionAlgebraDecodeBHist M)
                                                  (eilenbergMooreCompletionAlgebraDecodeBHist U)
                                                  (eilenbergMooreCompletionAlgebraDecodeBHist K)
                                                  (eilenbergMooreCompletionAlgebraDecodeBHist I)
                                                  (eilenbergMooreCompletionAlgebraDecodeBHist L)
                                                  (eilenbergMooreCompletionAlgebraDecodeBHist H)
                                                  (eilenbergMooreCompletionAlgebraDecodeBHist C)
                                                  (eilenbergMooreCompletionAlgebraDecodeBHist P)
                                                  (eilenbergMooreCompletionAlgebraDecodeBHist N))
                                          | _ :: _ => none

private theorem EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_round_trip
    (x : EilenbergMooreCompletionAlgebraUp) :
    eilenbergMooreCompletionAlgebraFromEventFlow
      (eilenbergMooreCompletionAlgebraToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M U K I L H C P N =>
      change
        some
          (EilenbergMooreCompletionAlgebraUp.mk
            (eilenbergMooreCompletionAlgebraDecodeBHist
              (eilenbergMooreCompletionAlgebraEncodeBHist M))
            (eilenbergMooreCompletionAlgebraDecodeBHist
              (eilenbergMooreCompletionAlgebraEncodeBHist U))
            (eilenbergMooreCompletionAlgebraDecodeBHist
              (eilenbergMooreCompletionAlgebraEncodeBHist K))
            (eilenbergMooreCompletionAlgebraDecodeBHist
              (eilenbergMooreCompletionAlgebraEncodeBHist I))
            (eilenbergMooreCompletionAlgebraDecodeBHist
              (eilenbergMooreCompletionAlgebraEncodeBHist L))
            (eilenbergMooreCompletionAlgebraDecodeBHist
              (eilenbergMooreCompletionAlgebraEncodeBHist H))
            (eilenbergMooreCompletionAlgebraDecodeBHist
              (eilenbergMooreCompletionAlgebraEncodeBHist C))
            (eilenbergMooreCompletionAlgebraDecodeBHist
              (eilenbergMooreCompletionAlgebraEncodeBHist P))
            (eilenbergMooreCompletionAlgebraDecodeBHist
              (eilenbergMooreCompletionAlgebraEncodeBHist N))) =
          some (EilenbergMooreCompletionAlgebraUp.mk M U K I L H C P N)
      rw [EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode M,
        EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode U,
        EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode K,
        EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode I,
        EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode L,
        EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode H,
        EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode C,
        EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode P,
        EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode N]

private theorem EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EilenbergMooreCompletionAlgebraUp} :
    eilenbergMooreCompletionAlgebraToEventFlow x =
      eilenbergMooreCompletionAlgebraToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eilenbergMooreCompletionAlgebraFromEventFlow
          (eilenbergMooreCompletionAlgebraToEventFlow x) =
        eilenbergMooreCompletionAlgebraFromEventFlow
          (eilenbergMooreCompletionAlgebraToEventFlow y) :=
    congrArg eilenbergMooreCompletionAlgebraFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_round_trip y)))

private theorem EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : EilenbergMooreCompletionAlgebraUp,
      eilenbergMooreCompletionAlgebraFields x =
        eilenbergMooreCompletionAlgebraFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ U₁ K₁ I₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ U₂ K₂ I₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance eilenbergMooreCompletionAlgebraBHistCarrier :
    BHistCarrier EilenbergMooreCompletionAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eilenbergMooreCompletionAlgebraToEventFlow
  fromEventFlow := eilenbergMooreCompletionAlgebraFromEventFlow

instance eilenbergMooreCompletionAlgebraChapterTasteGate :
    ChapterTasteGate EilenbergMooreCompletionAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      eilenbergMooreCompletionAlgebraFromEventFlow
        (eilenbergMooreCompletionAlgebraToEventFlow x) = some x
    exact EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance eilenbergMooreCompletionAlgebraFieldFaithful :
    FieldFaithful EilenbergMooreCompletionAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eilenbergMooreCompletionAlgebraFields
  field_faithful :=
    EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_fields_faithful

instance eilenbergMooreCompletionAlgebraNontrivial :
    Nontrivial EilenbergMooreCompletionAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EilenbergMooreCompletionAlgebraUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EilenbergMooreCompletionAlgebraUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate EilenbergMooreCompletionAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  eilenbergMooreCompletionAlgebraChapterTasteGate

theorem EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      eilenbergMooreCompletionAlgebraDecodeBHist
        (eilenbergMooreCompletionAlgebraEncodeBHist h) = h) ∧
      (∀ x : EilenbergMooreCompletionAlgebraUp,
        eilenbergMooreCompletionAlgebraFromEventFlow
          (eilenbergMooreCompletionAlgebraToEventFlow x) = some x) ∧
        (∀ x y : EilenbergMooreCompletionAlgebraUp,
          eilenbergMooreCompletionAlgebraToEventFlow x =
            eilenbergMooreCompletionAlgebraToEventFlow y → x = y) ∧
          eilenbergMooreCompletionAlgebraEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_decode_encode,
      EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        EilenbergMooreCompletionAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.EilenbergMooreCompletionAlgebraUp
