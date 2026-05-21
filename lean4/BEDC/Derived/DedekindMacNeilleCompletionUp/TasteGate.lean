import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindMacNeilleCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindMacNeilleCompletionUp : Type where
  | mk (L U K Q E H C P N : BHist) : DedekindMacNeilleCompletionUp
  deriving DecidableEq

def dedekindMacNeilleCompletionEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindMacNeilleCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindMacNeilleCompletionEncodeBHist h

def dedekindMacNeilleCompletionDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindMacNeilleCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindMacNeilleCompletionDecodeBHist tail)

private theorem dedekindMacNeilleCompletion_decode_encode :
    ∀ h : BHist,
      dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dedekindMacNeilleCompletionFields :
    DedekindMacNeilleCompletionUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | DedekindMacNeilleCompletionUp.mk L U K Q E H C P N => [L, U, K, Q, E, H, C, P, N]

def dedekindMacNeilleCompletionToEventFlow :
    DedekindMacNeilleCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | DedekindMacNeilleCompletionUp.mk L U K Q E H C P N =>
      [dedekindMacNeilleCompletionEncodeBHist L,
        dedekindMacNeilleCompletionEncodeBHist U,
        dedekindMacNeilleCompletionEncodeBHist K,
        dedekindMacNeilleCompletionEncodeBHist Q,
        dedekindMacNeilleCompletionEncodeBHist E,
        dedekindMacNeilleCompletionEncodeBHist H,
        dedekindMacNeilleCompletionEncodeBHist C,
        dedekindMacNeilleCompletionEncodeBHist P,
        dedekindMacNeilleCompletionEncodeBHist N]

private def dedekindMacNeilleCompletionEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dedekindMacNeilleCompletionEventAt index rest

def dedekindMacNeilleCompletionFromEventFlow :
    EventFlow → Option DedekindMacNeilleCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (DedekindMacNeilleCompletionUp.mk
        (dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEventAt 0 ef))
        (dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEventAt 1 ef))
        (dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEventAt 2 ef))
        (dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEventAt 3 ef))
        (dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEventAt 4 ef))
        (dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEventAt 5 ef))
        (dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEventAt 6 ef))
        (dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEventAt 7 ef))
        (dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEventAt 8 ef)))

private theorem dedekindMacNeilleCompletion_round_trip :
    ∀ x : DedekindMacNeilleCompletionUp,
      dedekindMacNeilleCompletionFromEventFlow
          (dedekindMacNeilleCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U K Q E H C P N =>
      change
        some
          (DedekindMacNeilleCompletionUp.mk
            (dedekindMacNeilleCompletionDecodeBHist
              (dedekindMacNeilleCompletionEncodeBHist L))
            (dedekindMacNeilleCompletionDecodeBHist
              (dedekindMacNeilleCompletionEncodeBHist U))
            (dedekindMacNeilleCompletionDecodeBHist
              (dedekindMacNeilleCompletionEncodeBHist K))
            (dedekindMacNeilleCompletionDecodeBHist
              (dedekindMacNeilleCompletionEncodeBHist Q))
            (dedekindMacNeilleCompletionDecodeBHist
              (dedekindMacNeilleCompletionEncodeBHist E))
            (dedekindMacNeilleCompletionDecodeBHist
              (dedekindMacNeilleCompletionEncodeBHist H))
            (dedekindMacNeilleCompletionDecodeBHist
              (dedekindMacNeilleCompletionEncodeBHist C))
            (dedekindMacNeilleCompletionDecodeBHist
              (dedekindMacNeilleCompletionEncodeBHist P))
            (dedekindMacNeilleCompletionDecodeBHist
              (dedekindMacNeilleCompletionEncodeBHist N))) =
          some (DedekindMacNeilleCompletionUp.mk L U K Q E H C P N)
      rw [dedekindMacNeilleCompletion_decode_encode L,
        dedekindMacNeilleCompletion_decode_encode U,
        dedekindMacNeilleCompletion_decode_encode K,
        dedekindMacNeilleCompletion_decode_encode Q,
        dedekindMacNeilleCompletion_decode_encode E,
        dedekindMacNeilleCompletion_decode_encode H,
        dedekindMacNeilleCompletion_decode_encode C,
        dedekindMacNeilleCompletion_decode_encode P,
        dedekindMacNeilleCompletion_decode_encode N]

private theorem dedekindMacNeilleCompletionToEventFlow_injective
    {x y : DedekindMacNeilleCompletionUp} :
    dedekindMacNeilleCompletionToEventFlow x =
        dedekindMacNeilleCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x =
          dedekindMacNeilleCompletionFromEventFlow
            (dedekindMacNeilleCompletionToEventFlow x) :=
        (dedekindMacNeilleCompletion_round_trip x).symm
      _ =
          dedekindMacNeilleCompletionFromEventFlow
            (dedekindMacNeilleCompletionToEventFlow y) :=
        congrArg dedekindMacNeilleCompletionFromEventFlow hxy
      _ = some y := dedekindMacNeilleCompletion_round_trip y
  exact Option.some.inj hsome

private theorem dedekindMacNeilleCompletion_field_faithful :
    ∀ x y : DedekindMacNeilleCompletionUp,
      dedekindMacNeilleCompletionFields x =
          dedekindMacNeilleCompletionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 K1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 K2 Q2 E2 H2 C2 P2 N2 =>
          injection hfields with hL tail0
          injection tail0 with hU tail1
          injection tail1 with hK tail2
          injection tail2 with hQ tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hL
          subst hU
          subst hK
          subst hQ
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance dedekindMacNeilleCompletionBHistCarrier :
    BHistCarrier DedekindMacNeilleCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindMacNeilleCompletionToEventFlow
  fromEventFlow := dedekindMacNeilleCompletionFromEventFlow

instance dedekindMacNeilleCompletionChapterTasteGate :
    ChapterTasteGate DedekindMacNeilleCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindMacNeilleCompletionFromEventFlow
          (dedekindMacNeilleCompletionToEventFlow x) =
        some x
    exact dedekindMacNeilleCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindMacNeilleCompletionToEventFlow_injective heq)

instance dedekindMacNeilleCompletionFieldFaithful :
    FieldFaithful DedekindMacNeilleCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dedekindMacNeilleCompletionFields
  field_faithful := dedekindMacNeilleCompletion_field_faithful

instance dedekindMacNeilleCompletionNontrivial :
    Nontrivial DedekindMacNeilleCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DedekindMacNeilleCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DedekindMacNeilleCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DedekindMacNeilleCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindMacNeilleCompletionChapterTasteGate

theorem DedekindMacNeilleCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dedekindMacNeilleCompletionDecodeBHist
          (dedekindMacNeilleCompletionEncodeBHist h) =
        h) ∧
      (∀ x : DedekindMacNeilleCompletionUp,
        dedekindMacNeilleCompletionFromEventFlow
            (dedekindMacNeilleCompletionToEventFlow x) =
          some x) ∧
      (∀ x y : DedekindMacNeilleCompletionUp,
        dedekindMacNeilleCompletionToEventFlow x =
            dedekindMacNeilleCompletionToEventFlow y →
          x = y) ∧
      dedekindMacNeilleCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨dedekindMacNeilleCompletion_decode_encode,
      dedekindMacNeilleCompletion_round_trip,
      fun _ _ hxy => dedekindMacNeilleCompletionToEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.DedekindMacNeilleCompletionUp.TasteGate
