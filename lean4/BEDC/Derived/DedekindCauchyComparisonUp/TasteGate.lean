import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindCauchyComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindCauchyComparisonUp : Type where
  | mk (D R W T E H C P N : BHist) : DedekindCauchyComparisonUp
  deriving DecidableEq

def dedekindCauchyComparisonEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindCauchyComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindCauchyComparisonEncodeBHist h

def dedekindCauchyComparisonDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindCauchyComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindCauchyComparisonDecodeBHist tail)

private theorem DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dedekindCauchyComparisonFields : DedekindCauchyComparisonUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | DedekindCauchyComparisonUp.mk D R W T E H C P N => [D, R, W, T, E, H, C, P, N]

def dedekindCauchyComparisonToEventFlow : DedekindCauchyComparisonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | DedekindCauchyComparisonUp.mk D R W T E H C P N =>
      [dedekindCauchyComparisonEncodeBHist D,
        dedekindCauchyComparisonEncodeBHist R,
        dedekindCauchyComparisonEncodeBHist W,
        dedekindCauchyComparisonEncodeBHist T,
        dedekindCauchyComparisonEncodeBHist E,
        dedekindCauchyComparisonEncodeBHist H,
        dedekindCauchyComparisonEncodeBHist C,
        dedekindCauchyComparisonEncodeBHist P,
        dedekindCauchyComparisonEncodeBHist N]

private def dedekindCauchyComparisonEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dedekindCauchyComparisonEventAt index rest

def dedekindCauchyComparisonFromEventFlow :
    EventFlow → Option DedekindCauchyComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (DedekindCauchyComparisonUp.mk
        (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEventAt 0 ef))
        (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEventAt 1 ef))
        (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEventAt 2 ef))
        (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEventAt 3 ef))
        (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEventAt 4 ef))
        (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEventAt 5 ef))
        (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEventAt 6 ef))
        (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEventAt 7 ef))
        (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEventAt 8 ef)))

private theorem dedekindCauchyComparison_round_trip :
    ∀ x : DedekindCauchyComparisonUp,
      dedekindCauchyComparisonFromEventFlow (dedekindCauchyComparisonToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D R W T E H C P N =>
      change
        some
          (DedekindCauchyComparisonUp.mk
            (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist D))
            (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist R))
            (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist W))
            (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist T))
            (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist E))
            (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist H))
            (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist C))
            (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist P))
            (dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist N))) =
          some (DedekindCauchyComparisonUp.mk D R W T E H C P N)
      rw [DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode D,
        DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode R,
        DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode W,
        DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode T,
        DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode E,
        DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode H,
        DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode C,
        DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode P,
        DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode N]

private theorem dedekindCauchyComparisonToEventFlow_injective
    {x y : DedekindCauchyComparisonUp} :
    dedekindCauchyComparisonToEventFlow x = dedekindCauchyComparisonToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x =
          dedekindCauchyComparisonFromEventFlow (dedekindCauchyComparisonToEventFlow x) :=
        (dedekindCauchyComparison_round_trip x).symm
      _ =
          dedekindCauchyComparisonFromEventFlow (dedekindCauchyComparisonToEventFlow y) :=
        congrArg dedekindCauchyComparisonFromEventFlow hxy
      _ = some y := dedekindCauchyComparison_round_trip y
  exact Option.some.inj hsome

private theorem dedekindCauchyComparison_field_faithful :
    ∀ x y : DedekindCauchyComparisonUp,
      dedekindCauchyComparisonFields x = dedekindCauchyComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 R1 W1 T1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 R2 W2 T2 E2 H2 C2 P2 N2 =>
          injection hfields with hD tail0
          injection tail0 with hR tail1
          injection tail1 with hW tail2
          injection tail2 with hT tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hD
          subst hR
          subst hW
          subst hT
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance dedekindCauchyComparisonBHistCarrier :
    BHistCarrier DedekindCauchyComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindCauchyComparisonToEventFlow
  fromEventFlow := dedekindCauchyComparisonFromEventFlow

instance dedekindCauchyComparisonChapterTasteGate :
    ChapterTasteGate DedekindCauchyComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindCauchyComparisonFromEventFlow (dedekindCauchyComparisonToEventFlow x) =
        some x
    exact dedekindCauchyComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindCauchyComparisonToEventFlow_injective heq)

instance dedekindCauchyComparisonFieldFaithful :
    FieldFaithful DedekindCauchyComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dedekindCauchyComparisonFields
  field_faithful := dedekindCauchyComparison_field_faithful

instance dedekindCauchyComparisonNontrivial :
    Nontrivial DedekindCauchyComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DedekindCauchyComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DedekindCauchyComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DedekindCauchyComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindCauchyComparisonChapterTasteGate

theorem DedekindCauchyComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dedekindCauchyComparisonDecodeBHist (dedekindCauchyComparisonEncodeBHist h) = h) ∧
      (∀ x : DedekindCauchyComparisonUp,
        dedekindCauchyComparisonFromEventFlow
            (dedekindCauchyComparisonToEventFlow x) =
          some x) ∧
      (∀ x y : DedekindCauchyComparisonUp,
        dedekindCauchyComparisonToEventFlow x =
            dedekindCauchyComparisonToEventFlow y →
          x = y) ∧
      dedekindCauchyComparisonEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DedekindCauchyComparisonTasteGate_single_carrier_alignment_decode,
      dedekindCauchyComparison_round_trip,
      fun _ _ hxy => dedekindCauchyComparisonToEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.DedekindCauchyComparisonUp
