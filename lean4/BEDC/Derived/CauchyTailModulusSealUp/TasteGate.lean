import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailModulusSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailModulusSealUp : Type where
  | mk (M F X tau D W0 W1 Q0 Q1 E H C P N : BHist) :
      CauchyTailModulusSealUp
  deriving DecidableEq

def cauchyTailModulusSealEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailModulusSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailModulusSealEncodeBHist h

def cauchyTailModulusSealDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailModulusSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailModulusSealDecodeBHist tail)

private theorem cauchyTailModulusSealDecode_encode_bhist :
    ∀ h : BHist,
      cauchyTailModulusSealDecodeBHist
          (cauchyTailModulusSealEncodeBHist h) =
        h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyTailModulusSealFields : CauchyTailModulusSealUp → List BHist
  | CauchyTailModulusSealUp.mk M F X tau D W0 W1 Q0 Q1 E H C P N =>
      [M, F, X, tau, D, W0, W1, Q0, Q1, E, H, C, P, N]

def cauchyTailModulusSealToEventFlow : CauchyTailModulusSealUp → EventFlow
  | x => (cauchyTailModulusSealFields x).map cauchyTailModulusSealEncodeBHist

def cauchyTailModulusSealFromEventFlow : EventFlow → Option CauchyTailModulusSealUp
  | [M, F, X, tau, D, W0, W1, Q0, Q1, E, H, C, P, N] =>
      some
        (CauchyTailModulusSealUp.mk
          (cauchyTailModulusSealDecodeBHist M)
          (cauchyTailModulusSealDecodeBHist F)
          (cauchyTailModulusSealDecodeBHist X)
          (cauchyTailModulusSealDecodeBHist tau)
          (cauchyTailModulusSealDecodeBHist D)
          (cauchyTailModulusSealDecodeBHist W0)
          (cauchyTailModulusSealDecodeBHist W1)
          (cauchyTailModulusSealDecodeBHist Q0)
          (cauchyTailModulusSealDecodeBHist Q1)
          (cauchyTailModulusSealDecodeBHist E)
          (cauchyTailModulusSealDecodeBHist H)
          (cauchyTailModulusSealDecodeBHist C)
          (cauchyTailModulusSealDecodeBHist P)
          (cauchyTailModulusSealDecodeBHist N))
  | _ => none

private theorem cauchyTailModulusSeal_round_trip :
    ∀ x : CauchyTailModulusSealUp,
      cauchyTailModulusSealFromEventFlow (cauchyTailModulusSealToEventFlow x) =
        some x := by
  intro x
  cases x with
  | mk M F X tau D W0 W1 Q0 Q1 E H C P N =>
      change
        some
          (CauchyTailModulusSealUp.mk
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist M))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist F))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist X))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist tau))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist D))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist W0))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist W1))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist Q0))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist Q1))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist E))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist H))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist C))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist P))
            (cauchyTailModulusSealDecodeBHist (cauchyTailModulusSealEncodeBHist N))) =
          some (CauchyTailModulusSealUp.mk M F X tau D W0 W1 Q0 Q1 E H C P N)
      rw [cauchyTailModulusSealDecode_encode_bhist M,
        cauchyTailModulusSealDecode_encode_bhist F,
        cauchyTailModulusSealDecode_encode_bhist X,
        cauchyTailModulusSealDecode_encode_bhist tau,
        cauchyTailModulusSealDecode_encode_bhist D,
        cauchyTailModulusSealDecode_encode_bhist W0,
        cauchyTailModulusSealDecode_encode_bhist W1,
        cauchyTailModulusSealDecode_encode_bhist Q0,
        cauchyTailModulusSealDecode_encode_bhist Q1,
        cauchyTailModulusSealDecode_encode_bhist E,
        cauchyTailModulusSealDecode_encode_bhist H,
        cauchyTailModulusSealDecode_encode_bhist C,
        cauchyTailModulusSealDecode_encode_bhist P,
        cauchyTailModulusSealDecode_encode_bhist N]

private theorem cauchyTailModulusSealToEventFlow_injective
    {x y : CauchyTailModulusSealUp} :
    cauchyTailModulusSealToEventFlow x = cauchyTailModulusSealToEventFlow y → x = y := by
  intro heq
  have hread :
      cauchyTailModulusSealFromEventFlow (cauchyTailModulusSealToEventFlow x) =
        cauchyTailModulusSealFromEventFlow (cauchyTailModulusSealToEventFlow y) :=
    congrArg cauchyTailModulusSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailModulusSeal_round_trip x).symm
      (Eq.trans hread (cauchyTailModulusSeal_round_trip y)))

private theorem cauchyTailModulusSeal_fields_faithful :
    ∀ x y : CauchyTailModulusSealUp,
      cauchyTailModulusSealFields x = cauchyTailModulusSealFields y → x = y := by
  intro x y hfields
  cases x with
  | mk M F X tau D W0 W1 Q0 Q1 E H C P N =>
      cases y with
      | mk M' F' X' tau' D' W0' W1' Q0' Q1' E' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyTailModulusSealBHistCarrier : BHistCarrier CauchyTailModulusSealUp where
  toEventFlow := cauchyTailModulusSealToEventFlow
  fromEventFlow := cauchyTailModulusSealFromEventFlow

instance cauchyTailModulusSealChapterTasteGate :
    ChapterTasteGate CauchyTailModulusSealUp where
  round_trip := by
    intro x
    change cauchyTailModulusSealFromEventFlow
      (cauchyTailModulusSealToEventFlow x) = some x
    exact cauchyTailModulusSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailModulusSealToEventFlow_injective heq)

instance cauchyTailModulusSealFieldFaithful :
    FieldFaithful CauchyTailModulusSealUp where
  fields := cauchyTailModulusSealFields
  field_faithful := cauchyTailModulusSeal_fields_faithful

instance cauchyTailModulusSealNontrivial : Nontrivial CauchyTailModulusSealUp where
  witness_pair :=
    ⟨CauchyTailModulusSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyTailModulusSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyTailModulusSealUp :=
  cauchyTailModulusSealChapterTasteGate

theorem CauchyTailModulusSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyTailModulusSealDecodeBHist
          (cauchyTailModulusSealEncodeBHist h) =
        h) ∧
      (∃ x y : CauchyTailModulusSealUp, x ≠ y) ∧
        cauchyTailModulusSealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · exact
        ⟨CauchyTailModulusSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
          CauchyTailModulusSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
          by
            intro h
            cases h⟩
    · rfl

end BEDC.Derived.CauchyTailModulusSealUp
