import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BayesianUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BayesianUp : Type where
  | mk (Dpi Domega C pi lambda e omega beta H N P : BHist) : BayesianUp
  deriving DecidableEq

def BayesianTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BayesianTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: BayesianTasteGate_single_carrier_alignment_encodeBHist h

def BayesianTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (BayesianTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (BayesianTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BayesianTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BayesianTasteGate_single_carrier_alignment_decodeBHist
          (BayesianTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def BayesianTasteGate_single_carrier_alignment_fields :
    BayesianUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BayesianUp.mk Dpi Domega C pi lambda e omega beta H N P =>
      [Dpi, Domega, C, pi, lambda, e, omega, beta, H, N, P]

def BayesianTasteGate_single_carrier_alignment_toEventFlow :
    BayesianUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (BayesianTasteGate_single_carrier_alignment_fields x).map
      BayesianTasteGate_single_carrier_alignment_encodeBHist

def BayesianTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BayesianUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Dpi :: Domega :: C :: pi :: lambda :: e :: omega :: beta :: H :: N :: P :: [] =>
      some
        (BayesianUp.mk
          (BayesianTasteGate_single_carrier_alignment_decodeBHist Dpi)
          (BayesianTasteGate_single_carrier_alignment_decodeBHist Domega)
          (BayesianTasteGate_single_carrier_alignment_decodeBHist C)
          (BayesianTasteGate_single_carrier_alignment_decodeBHist pi)
          (BayesianTasteGate_single_carrier_alignment_decodeBHist lambda)
          (BayesianTasteGate_single_carrier_alignment_decodeBHist e)
          (BayesianTasteGate_single_carrier_alignment_decodeBHist omega)
          (BayesianTasteGate_single_carrier_alignment_decodeBHist beta)
          (BayesianTasteGate_single_carrier_alignment_decodeBHist H)
          (BayesianTasteGate_single_carrier_alignment_decodeBHist N)
          (BayesianTasteGate_single_carrier_alignment_decodeBHist P))
  | _ => none

private theorem BayesianTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BayesianUp,
      BayesianTasteGate_single_carrier_alignment_fromEventFlow
          (BayesianTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk Dpi Domega C pi lambda e omega beta H N P =>
      simp only [BayesianTasteGate_single_carrier_alignment_toEventFlow,
        BayesianTasteGate_single_carrier_alignment_fields,
        BayesianTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons, List.map_nil,
        BayesianTasteGate_single_carrier_alignment_decode_encode]

private theorem BayesianTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BayesianUp} :
    BayesianTasteGate_single_carrier_alignment_toEventFlow x =
        BayesianTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          BayesianTasteGate_single_carrier_alignment_fromEventFlow
            (BayesianTasteGate_single_carrier_alignment_toEventFlow x) :=
        (BayesianTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          BayesianTasteGate_single_carrier_alignment_fromEventFlow
            (BayesianTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg BayesianTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := BayesianTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem BayesianTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BayesianUp,
      BayesianTasteGate_single_carrier_alignment_fields x =
          BayesianTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Dpi₁ Domega₁ C₁ pi₁ lambda₁ e₁ omega₁ beta₁ H₁ N₁ P₁ =>
      cases y with
      | mk Dpi₂ Domega₂ C₂ pi₂ lambda₂ e₂ omega₂ beta₂ H₂ N₂ P₂ =>
          cases hfields
          rfl

instance BayesianTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BayesianUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BayesianTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BayesianTasteGate_single_carrier_alignment_fromEventFlow

instance BayesianTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BayesianUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BayesianTasteGate_single_carrier_alignment_fromEventFlow
          (BayesianTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BayesianTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BayesianTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance BayesianTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful BayesianUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BayesianTasteGate_single_carrier_alignment_fields
  field_faithful := BayesianTasteGate_single_carrier_alignment_field_faithful

instance BayesianTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial BayesianUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BayesianUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BayesianUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BayesianTasteGate_single_carrier_alignment :
    (forall Dpi Domega C pi lambda e omega beta H N P : BHist,
      BayesianTasteGate_single_carrier_alignment_fields
          (BayesianUp.mk Dpi Domega C pi lambda e omega beta H N P) =
        [Dpi, Domega, C, pi, lambda, e, omega, beta, H, N, P]) ∧
      BayesianTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨(fun _ _ _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.BayesianUp
