import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindCutCauchyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindCutCauchyBoundaryUp : Type where
  | mk (L U K Q S R D E H C P N : BHist) : DedekindCutCauchyBoundaryUp
  deriving DecidableEq

def dedekindCutCauchyBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindCutCauchyBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindCutCauchyBoundaryEncodeBHist h

def dedekindCutCauchyBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindCutCauchyBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindCutCauchyBoundaryDecodeBHist tail)

private theorem dedekindCutCauchyBoundary_decode_encode :
    ∀ h : BHist,
      dedekindCutCauchyBoundaryDecodeBHist
          (dedekindCutCauchyBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dedekindCutCauchyBoundaryFields :
    DedekindCutCauchyBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindCutCauchyBoundaryUp.mk L U K Q S R D E H C P N =>
      [L, U, K, Q, S, R, D, E, H, C, P, N]

def dedekindCutCauchyBoundaryToEventFlow :
    DedekindCutCauchyBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (dedekindCutCauchyBoundaryFields x).map
      dedekindCutCauchyBoundaryEncodeBHist

private def dedekindCutCauchyBoundaryEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      dedekindCutCauchyBoundaryEventAtDefault index rest

def dedekindCutCauchyBoundaryFromEventFlow
    (ef : EventFlow) : Option DedekindCutCauchyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DedekindCutCauchyBoundaryUp.mk
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 0 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 1 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 2 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 3 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 4 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 5 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 6 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 7 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 8 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 9 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 10 ef))
      (dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEventAtDefault 11 ef)))

private theorem dedekindCutCauchyBoundary_round_trip :
    ∀ x : DedekindCutCauchyBoundaryUp,
      dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U K Q S R D E H C P N =>
      change
        some
          (DedekindCutCauchyBoundaryUp.mk
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist L))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist U))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist K))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist Q))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist S))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist R))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist D))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist E))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist H))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist C))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist P))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist N))) =
          some (DedekindCutCauchyBoundaryUp.mk L U K Q S R D E H C P N)
      rw [dedekindCutCauchyBoundary_decode_encode L,
        dedekindCutCauchyBoundary_decode_encode U,
        dedekindCutCauchyBoundary_decode_encode K,
        dedekindCutCauchyBoundary_decode_encode Q,
        dedekindCutCauchyBoundary_decode_encode S,
        dedekindCutCauchyBoundary_decode_encode R,
        dedekindCutCauchyBoundary_decode_encode D,
        dedekindCutCauchyBoundary_decode_encode E,
        dedekindCutCauchyBoundary_decode_encode H,
        dedekindCutCauchyBoundary_decode_encode C,
        dedekindCutCauchyBoundary_decode_encode P,
        dedekindCutCauchyBoundary_decode_encode N]

private theorem dedekindCutCauchyBoundaryToEventFlow_injective
    {x y : DedekindCutCauchyBoundaryUp} :
    dedekindCutCauchyBoundaryToEventFlow x =
        dedekindCutCauchyBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow x) =
        dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow y) :=
    congrArg dedekindCutCauchyBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (dedekindCutCauchyBoundary_round_trip x).symm
      (Eq.trans hread (dedekindCutCauchyBoundary_round_trip y)))

private theorem dedekindCutCauchyBoundary_field_faithful :
    ∀ x y : DedekindCutCauchyBoundaryUp,
      dedekindCutCauchyBoundaryFields x =
          dedekindCutCauchyBoundaryFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 K1 Q1 S1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 K2 Q2 S2 R2 D2 E2 H2 C2 P2 N2 =>
          injection hfields with hL t1
          injection t1 with hU t2
          injection t2 with hK t3
          injection t3 with hQ t4
          injection t4 with hS t5
          injection t5 with hR t6
          injection t6 with hD t7
          injection t7 with hE t8
          injection t8 with hH t9
          injection t9 with hC t10
          injection t10 with hP t11
          injection t11 with hN _
          subst hL
          subst hU
          subst hK
          subst hQ
          subst hS
          subst hR
          subst hD
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance dedekindCutCauchyBoundaryBHistCarrier :
    BHistCarrier DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindCutCauchyBoundaryToEventFlow
  fromEventFlow := dedekindCutCauchyBoundaryFromEventFlow

instance dedekindCutCauchyBoundaryChapterTasteGate :
    ChapterTasteGate DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow x) =
        some x
    exact dedekindCutCauchyBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindCutCauchyBoundaryToEventFlow_injective heq)

instance dedekindCutCauchyBoundaryFieldFaithful :
    FieldFaithful DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dedekindCutCauchyBoundaryFields
  field_faithful := dedekindCutCauchyBoundary_field_faithful

instance dedekindCutCauchyBoundaryNontrivial :
    Nontrivial DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DedekindCutCauchyBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      DedekindCutCauchyBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DedekindCutCauchyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindCutCauchyBoundaryChapterTasteGate

theorem DedekindCutCauchyBoundaryUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dedekindCutCauchyBoundaryDecodeBHist
          (dedekindCutCauchyBoundaryEncodeBHist h) =
        h) ∧
      (∀ x : DedekindCutCauchyBoundaryUp,
        dedekindCutCauchyBoundaryFromEventFlow
            (dedekindCutCauchyBoundaryToEventFlow x) =
          some x) ∧
      (∀ x y : DedekindCutCauchyBoundaryUp,
        dedekindCutCauchyBoundaryToEventFlow x =
            dedekindCutCauchyBoundaryToEventFlow y →
          x = y) ∧
      dedekindCutCauchyBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨dedekindCutCauchyBoundary_decode_encode,
      dedekindCutCauchyBoundary_round_trip,
      fun _ _ heq => dedekindCutCauchyBoundaryToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DedekindCutCauchyBoundaryUp
