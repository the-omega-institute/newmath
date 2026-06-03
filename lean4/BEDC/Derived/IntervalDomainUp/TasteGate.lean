import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalDomainUp : Type where
  | mk
      (L R N W Q E H C P A : BHist) :
      IntervalDomainUp
  deriving DecidableEq

def IntervalDomainTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: IntervalDomainTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: IntervalDomainTasteGate_single_carrier_alignment_encodeBHist h

def IntervalDomainTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem IntervalDomainTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
          (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def IntervalDomainTasteGate_single_carrier_alignment_fields :
    IntervalDomainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalDomainUp.mk L R N W Q E H C P A => [L, R, N, W, Q, E, H, C, P, A]

def IntervalDomainTasteGate_single_carrier_alignment_toEventFlow :
    IntervalDomainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (IntervalDomainTasteGate_single_carrier_alignment_fields x).map
        IntervalDomainTasteGate_single_carrier_alignment_encodeBHist

def IntervalDomainTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option IntervalDomainUp
  -- BEDC touchpoint anchor: BHist BMark
  | [L, R, N, W, Q, E, H, C, P, A] =>
      some
        (IntervalDomainUp.mk
          (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist L)
          (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist R)
          (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist N)
          (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist W)
          (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist Q)
          (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist E)
          (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist H)
          (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist C)
          (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist P)
          (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist A))
  | _ => none

private theorem IntervalDomainTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IntervalDomainUp,
      IntervalDomainTasteGate_single_carrier_alignment_fromEventFlow
          (IntervalDomainTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R N W Q E H C P A =>
      change
        some
          (IntervalDomainUp.mk
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist L))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist R))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist N))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist W))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist Q))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist E))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist H))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist C))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist P))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist A))) =
          some (IntervalDomainUp.mk L R N W Q E H C P A)
      rw [IntervalDomainTasteGate_single_carrier_alignment_decode_encode L,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode R,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode N,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode W,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode Q,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode E,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode H,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode C,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode P,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode A]

private theorem IntervalDomainTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IntervalDomainUp} :
    IntervalDomainTasteGate_single_carrier_alignment_toEventFlow x =
        IntervalDomainTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      IntervalDomainTasteGate_single_carrier_alignment_fromEventFlow
          (IntervalDomainTasteGate_single_carrier_alignment_toEventFlow x) =
        IntervalDomainTasteGate_single_carrier_alignment_fromEventFlow
          (IntervalDomainTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg IntervalDomainTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (IntervalDomainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IntervalDomainTasteGate_single_carrier_alignment_round_trip y)))

private theorem IntervalDomainTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : IntervalDomainUp,
      IntervalDomainTasteGate_single_carrier_alignment_fields x =
          IntervalDomainTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ R₁ N₁ W₁ Q₁ E₁ H₁ C₁ P₁ A₁ =>
      cases y with
      | mk L₂ R₂ N₂ W₂ Q₂ E₂ H₂ C₂ P₂ A₂ =>
          cases hfields
          rfl

instance IntervalDomainTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier IntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := IntervalDomainTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := IntervalDomainTasteGate_single_carrier_alignment_fromEventFlow

instance IntervalDomainTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate IntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      IntervalDomainTasteGate_single_carrier_alignment_fromEventFlow
          (IntervalDomainTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact IntervalDomainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntervalDomainTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance IntervalDomainTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful IntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := IntervalDomainTasteGate_single_carrier_alignment_fields
  field_faithful := IntervalDomainTasteGate_single_carrier_alignment_fields_faithful

instance IntervalDomainTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial IntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IntervalDomainUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      IntervalDomainUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem IntervalDomainTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
          (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      IntervalDomainTasteGate_single_carrier_alignment_fields
          (IntervalDomainUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact IntervalDomainTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.IntervalDomainUp
