import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# AxisCarryRouteSeparationUp TasteGate carrier.
-/

namespace BEDC.Derived.AxisCarryRouteSeparationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Single carrier for the axis carry route separation packet. -/
inductive AxisCarryRouteSeparationUp : Type where
  | mk :
      (A U D S T B R H C P N : BHist) →
      AxisCarryRouteSeparationUp
  deriving DecidableEq

def axisCarryRouteSeparationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisCarryRouteSeparationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisCarryRouteSeparationEncodeBHist h

def axisCarryRouteSeparationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisCarryRouteSeparationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisCarryRouteSeparationDecodeBHist tail)

private theorem axisCarryRouteSeparationDecode_encode_bhist :
    ∀ h : BHist,
      axisCarryRouteSeparationDecodeBHist
        (axisCarryRouteSeparationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axisCarryRouteSeparationToEventFlow :
    AxisCarryRouteSeparationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisCarryRouteSeparationUp.mk A U D S T B R H C P N =>
      [[BMark.b0],
        axisCarryRouteSeparationEncodeBHist A,
        [BMark.b1, BMark.b0],
        axisCarryRouteSeparationEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        axisCarryRouteSeparationEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryRouteSeparationEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryRouteSeparationEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryRouteSeparationEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryRouteSeparationEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axisCarryRouteSeparationEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        axisCarryRouteSeparationEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        axisCarryRouteSeparationEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryRouteSeparationEncodeBHist N]

def axisCarryRouteSeparationFromEventFlow :
    EventFlow → Option AxisCarryRouteSeparationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagA :: restA =>
      match restA with
      | [] => none
      | A :: restU0 =>
          match restU0 with
          | [] => none
          | _tagU :: restU =>
              match restU with
              | [] => none
              | U :: restD0 =>
                  match restD0 with
                  | [] => none
                  | _tagD :: restD =>
                      match restD with
                      | [] => none
                      | D :: restS0 =>
                          match restS0 with
                          | [] => none
                          | _tagS :: restS =>
                              match restS with
                              | [] => none
                              | S :: restT0 =>
                                  match restT0 with
                                  | [] => none
                                  | _tagT :: restT =>
                                      match restT with
                                      | [] => none
                                      | T :: restB0 =>
                                          match restB0 with
                                          | [] => none
                                          | _tagB :: restB =>
                                              match restB with
                                              | [] => none
                                              | B :: restR0 =>
                                                  match restR0 with
                                                  | [] => none
                                                  | _tagR :: restR =>
                                                      match restR with
                                                      | [] => none
                                                      | R :: restH0 =>
                                                          match restH0 with
                                                          | [] => none
                                                          | _tagH :: restH =>
                                                              match restH with
                                                              | [] => none
                                                              | H :: restC0 =>
                                                                  match restC0 with
                                                                  | [] => none
                                                                  | _tagC :: restC =>
                                                                      match restC with
                                                                      | [] => none
                                                                      | C :: restP0 =>
                                                                          match restP0 with
                                                                          | [] => none
                                                                          | _tagP :: restP =>
                                                                              match restP with
                                                                              | [] => none
                                                                              | P :: restN0 =>
                                                                                  match restN0 with
                                                                                  | [] => none
                                                                                  | _tagN :: restN =>
                                                                                      match restN with
                                                                                      | [] => none
                                                                                      | N :: restFinal =>
                                                                                          match restFinal with
                                                                                          | [] =>
                                                                                              some
                                                                                                (AxisCarryRouteSeparationUp.mk
                                                                                                  (axisCarryRouteSeparationDecodeBHist A)
                                                                                                  (axisCarryRouteSeparationDecodeBHist U)
                                                                                                  (axisCarryRouteSeparationDecodeBHist D)
                                                                                                  (axisCarryRouteSeparationDecodeBHist S)
                                                                                                  (axisCarryRouteSeparationDecodeBHist T)
                                                                                                  (axisCarryRouteSeparationDecodeBHist B)
                                                                                                  (axisCarryRouteSeparationDecodeBHist R)
                                                                                                  (axisCarryRouteSeparationDecodeBHist H)
                                                                                                  (axisCarryRouteSeparationDecodeBHist C)
                                                                                                  (axisCarryRouteSeparationDecodeBHist P)
                                                                                                  (axisCarryRouteSeparationDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem axisCarryRouteSeparation_round_trip :
    ∀ x : AxisCarryRouteSeparationUp,
      axisCarryRouteSeparationFromEventFlow
        (axisCarryRouteSeparationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A U D S T B R H C P N =>
      change
        some
          (AxisCarryRouteSeparationUp.mk
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist A))
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist U))
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist D))
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist S))
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist T))
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist B))
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist R))
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist H))
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist C))
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist P))
            (axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist N))) =
          some (AxisCarryRouteSeparationUp.mk A U D S T B R H C P N)
      rw [axisCarryRouteSeparationDecode_encode_bhist A,
        axisCarryRouteSeparationDecode_encode_bhist U,
        axisCarryRouteSeparationDecode_encode_bhist D,
        axisCarryRouteSeparationDecode_encode_bhist S,
        axisCarryRouteSeparationDecode_encode_bhist T,
        axisCarryRouteSeparationDecode_encode_bhist B,
        axisCarryRouteSeparationDecode_encode_bhist R,
        axisCarryRouteSeparationDecode_encode_bhist H,
        axisCarryRouteSeparationDecode_encode_bhist C,
        axisCarryRouteSeparationDecode_encode_bhist P,
        axisCarryRouteSeparationDecode_encode_bhist N]

private theorem axisCarryRouteSeparationToEventFlow_injective
    {x y : AxisCarryRouteSeparationUp} :
    axisCarryRouteSeparationToEventFlow x =
      axisCarryRouteSeparationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisCarryRouteSeparationFromEventFlow
          (axisCarryRouteSeparationToEventFlow x) =
        axisCarryRouteSeparationFromEventFlow
          (axisCarryRouteSeparationToEventFlow y) :=
    congrArg axisCarryRouteSeparationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axisCarryRouteSeparation_round_trip x).symm
      (Eq.trans hread (axisCarryRouteSeparation_round_trip y)))

instance axisCarryRouteSeparationBHistCarrier :
    BHistCarrier AxisCarryRouteSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisCarryRouteSeparationToEventFlow
  fromEventFlow := axisCarryRouteSeparationFromEventFlow

instance axisCarryRouteSeparationChapterTasteGate :
    ChapterTasteGate AxisCarryRouteSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      axisCarryRouteSeparationFromEventFlow
        (axisCarryRouteSeparationToEventFlow x) = some x
    exact axisCarryRouteSeparation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axisCarryRouteSeparationToEventFlow_injective heq)

instance axisCarryRouteSeparationFieldFaithful :
    FieldFaithful AxisCarryRouteSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AxisCarryRouteSeparationUp.mk A U D S T B R H C P N =>
        [A, U, D, S, T, B, R, H, C, P, N]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk A U D S T B R H C P N =>
        cases y with
        | mk A' U' D' S' T' B' R' H' C' P' N' =>
            cases hfields
            rfl

instance axisCarryRouteSeparationNontrivial :
    Nontrivial AxisCarryRouteSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxisCarryRouteSeparationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxisCarryRouteSeparationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxisCarryRouteSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axisCarryRouteSeparationChapterTasteGate

theorem AxisCarryRouteSeparationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AxisCarryRouteSeparationUp) ∧
      Nonempty (FieldFaithful AxisCarryRouteSeparationUp) ∧
        Nonempty (Nontrivial AxisCarryRouteSeparationUp) ∧
          (∀ h : BHist,
            axisCarryRouteSeparationDecodeBHist
              (axisCarryRouteSeparationEncodeBHist h) = h) ∧
            (∀ x : AxisCarryRouteSeparationUp,
              axisCarryRouteSeparationFromEventFlow
                (axisCarryRouteSeparationToEventFlow x) = some x) ∧
              (∀ x y : AxisCarryRouteSeparationUp,
                axisCarryRouteSeparationToEventFlow x =
                  axisCarryRouteSeparationToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨axisCarryRouteSeparationChapterTasteGate⟩,
      ⟨axisCarryRouteSeparationFieldFaithful⟩,
      ⟨axisCarryRouteSeparationNontrivial⟩,
      axisCarryRouteSeparationDecode_encode_bhist,
      axisCarryRouteSeparation_round_trip,
      fun x y heq => axisCarryRouteSeparationToEventFlow_injective heq⟩

end BEDC.Derived.AxisCarryRouteSeparationUp
