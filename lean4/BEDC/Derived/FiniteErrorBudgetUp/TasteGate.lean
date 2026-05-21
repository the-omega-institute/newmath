import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteErrorBudgetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteErrorBudgetUp : Type where
  | mk (n epsilon b d t r e P N : BHist) : FiniteErrorBudgetUp
  deriving DecidableEq

def finiteErrorBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteErrorBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteErrorBudgetEncodeBHist h

def finiteErrorBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteErrorBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteErrorBudgetDecodeBHist tail)

private theorem finiteErrorBudgetDecode_encode_bhist :
    ∀ h : BHist, finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteErrorBudgetToEventFlow : FiniteErrorBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteErrorBudgetUp.mk n epsilon b d t r e P N =>
      [[BMark.b0],
        finiteErrorBudgetEncodeBHist n,
        [BMark.b1, BMark.b0],
        finiteErrorBudgetEncodeBHist epsilon,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteErrorBudgetEncodeBHist b,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteErrorBudgetEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteErrorBudgetEncodeBHist t,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteErrorBudgetEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteErrorBudgetEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteErrorBudgetEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteErrorBudgetEncodeBHist N]

def finiteErrorBudgetFromEventFlow : EventFlow → Option FiniteErrorBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tagN :: n :: _tagEpsilon :: epsilon :: _tagB :: b :: _tagD :: d :: _tagT :: t ::
      _tagR :: r :: _tagE :: e :: _tagP :: P :: _tagName :: N :: [] =>
      some
        (FiniteErrorBudgetUp.mk
          (finiteErrorBudgetDecodeBHist n)
          (finiteErrorBudgetDecodeBHist epsilon)
          (finiteErrorBudgetDecodeBHist b)
          (finiteErrorBudgetDecodeBHist d)
          (finiteErrorBudgetDecodeBHist t)
          (finiteErrorBudgetDecodeBHist r)
          (finiteErrorBudgetDecodeBHist e)
          (finiteErrorBudgetDecodeBHist P)
          (finiteErrorBudgetDecodeBHist N))
  | _ => none

private theorem finiteErrorBudget_round_trip :
    ∀ x : FiniteErrorBudgetUp,
      finiteErrorBudgetFromEventFlow (finiteErrorBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk n epsilon b d t r e P N =>
      change
        some
          (FiniteErrorBudgetUp.mk
            (finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist n))
            (finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist epsilon))
            (finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist b))
            (finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist d))
            (finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist t))
            (finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist r))
            (finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist e))
            (finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist P))
            (finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist N))) =
          some (FiniteErrorBudgetUp.mk n epsilon b d t r e P N)
      rw [finiteErrorBudgetDecode_encode_bhist n, finiteErrorBudgetDecode_encode_bhist epsilon,
        finiteErrorBudgetDecode_encode_bhist b, finiteErrorBudgetDecode_encode_bhist d,
        finiteErrorBudgetDecode_encode_bhist t, finiteErrorBudgetDecode_encode_bhist r,
        finiteErrorBudgetDecode_encode_bhist e, finiteErrorBudgetDecode_encode_bhist P,
        finiteErrorBudgetDecode_encode_bhist N]

private theorem finiteErrorBudgetToEventFlow_injective {x y : FiniteErrorBudgetUp} :
    finiteErrorBudgetToEventFlow x = finiteErrorBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteErrorBudgetFromEventFlow (finiteErrorBudgetToEventFlow x) =
        finiteErrorBudgetFromEventFlow (finiteErrorBudgetToEventFlow y) :=
    congrArg finiteErrorBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteErrorBudget_round_trip x).symm
      (Eq.trans hread (finiteErrorBudget_round_trip y)))

private def finiteErrorBudgetFields : FiniteErrorBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteErrorBudgetUp.mk n epsilon b d t r e P N => [n, epsilon, b, d, t, r, e, P, N]

private theorem finiteErrorBudget_fields_faithful :
    ∀ x y : FiniteErrorBudgetUp,
      finiteErrorBudgetFields x = finiteErrorBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk n1 epsilon1 b1 d1 t1 r1 e1 P1 N1 =>
      cases y with
      | mk n2 epsilon2 b2 d2 t2 r2 e2 P2 N2 =>
          cases hfields
          rfl

instance finiteErrorBudgetBHistCarrier : BHistCarrier FiniteErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteErrorBudgetToEventFlow
  fromEventFlow := finiteErrorBudgetFromEventFlow

instance finiteErrorBudgetChapterTasteGate : ChapterTasteGate FiniteErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteErrorBudgetFromEventFlow (finiteErrorBudgetToEventFlow x) = some x
    exact finiteErrorBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteErrorBudgetToEventFlow_injective heq)

instance finiteErrorBudgetFieldFaithful : FieldFaithful FiniteErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteErrorBudgetFields
  field_faithful := finiteErrorBudget_fields_faithful

instance finiteErrorBudgetNontrivial : Nontrivial FiniteErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteErrorBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteErrorBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def FiniteErrorBudgetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteErrorBudgetUp) ∧
      Nonempty (FieldFaithful FiniteErrorBudgetUp) ∧
      Nonempty (Nontrivial FiniteErrorBudgetUp) ∧
      (∀ h : BHist, finiteErrorBudgetDecodeBHist (finiteErrorBudgetEncodeBHist h) = h) ∧
      (∀ x : FiniteErrorBudgetUp,
        finiteErrorBudgetFromEventFlow (finiteErrorBudgetToEventFlow x) = some x) ∧
      (∀ x y : FiniteErrorBudgetUp,
        finiteErrorBudgetToEventFlow x = finiteErrorBudgetToEventFlow y → x = y) ∧
      finiteErrorBudgetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact
      ⟨{
        round_trip := by
          intro x
          change finiteErrorBudgetFromEventFlow (finiteErrorBudgetToEventFlow x) = some x
          exact finiteErrorBudget_round_trip x
        layer_separation := by
          intro x y hxy heq
          exact hxy (finiteErrorBudgetToEventFlow_injective heq)
      }⟩
  constructor
  · exact
      ⟨{
        fields := finiteErrorBudgetFields
        field_faithful := finiteErrorBudget_fields_faithful
      }⟩
  constructor
  · exact
      ⟨{
        witness_pair :=
          ⟨FiniteErrorBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            FiniteErrorBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            by
              intro h
              cases h⟩
      }⟩
  constructor
  · exact finiteErrorBudgetDecode_encode_bhist
  constructor
  · exact finiteErrorBudget_round_trip
  constructor
  · intro x y heq
    exact finiteErrorBudgetToEventFlow_injective heq
  · rfl

end BEDC.Derived.FiniteErrorBudgetUp.TasteGate
