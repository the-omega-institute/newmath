import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyMeanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyMeanUp : Type where
  | mk (S D W R A E H C P N : BHist) : BishopCauchyMeanUp
  deriving DecidableEq

def bishopCauchyMeanEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyMeanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyMeanEncodeBHist h

def bishopCauchyMeanDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyMeanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyMeanDecodeBHist tail)

private theorem BishopCauchyMeanTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyMeanFields : BishopCauchyMeanUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BishopCauchyMeanUp.mk S D W R A E H C P N => [S, D, W, R, A, E, H, C, P, N]

def bishopCauchyMeanToEventFlow : BishopCauchyMeanUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BishopCauchyMeanUp.mk S D W R A E H C P N =>
      [bishopCauchyMeanEncodeBHist S,
        bishopCauchyMeanEncodeBHist D,
        bishopCauchyMeanEncodeBHist W,
        bishopCauchyMeanEncodeBHist R,
        bishopCauchyMeanEncodeBHist A,
        bishopCauchyMeanEncodeBHist E,
        bishopCauchyMeanEncodeBHist H,
        bishopCauchyMeanEncodeBHist C,
        bishopCauchyMeanEncodeBHist P,
        bishopCauchyMeanEncodeBHist N]

private def bishopCauchyMeanEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyMeanEventAt index rest

def bishopCauchyMeanFromEventFlow : EventFlow → Option BishopCauchyMeanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BishopCauchyMeanUp.mk
        (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEventAt 0 ef))
        (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEventAt 1 ef))
        (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEventAt 2 ef))
        (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEventAt 3 ef))
        (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEventAt 4 ef))
        (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEventAt 5 ef))
        (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEventAt 6 ef))
        (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEventAt 7 ef))
        (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEventAt 8 ef))
        (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEventAt 9 ef)))

private theorem bishopCauchyMean_round_trip :
    ∀ x : BishopCauchyMeanUp,
      bishopCauchyMeanFromEventFlow (bishopCauchyMeanToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D W R A E H C P N =>
      change
        some
            (BishopCauchyMeanUp.mk
              (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist S))
              (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist D))
              (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist W))
              (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist R))
              (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist A))
              (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist E))
              (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist H))
              (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist C))
              (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist P))
              (bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist N))) =
          some (BishopCauchyMeanUp.mk S D W R A E H C P N)
      rw [BishopCauchyMeanTasteGate_single_carrier_alignment_decode S,
        BishopCauchyMeanTasteGate_single_carrier_alignment_decode D,
        BishopCauchyMeanTasteGate_single_carrier_alignment_decode W,
        BishopCauchyMeanTasteGate_single_carrier_alignment_decode R,
        BishopCauchyMeanTasteGate_single_carrier_alignment_decode A,
        BishopCauchyMeanTasteGate_single_carrier_alignment_decode E,
        BishopCauchyMeanTasteGate_single_carrier_alignment_decode H,
        BishopCauchyMeanTasteGate_single_carrier_alignment_decode C,
        BishopCauchyMeanTasteGate_single_carrier_alignment_decode P,
        BishopCauchyMeanTasteGate_single_carrier_alignment_decode N]

private theorem bishopCauchyMeanToEventFlow_injective {x y : BishopCauchyMeanUp} :
    bishopCauchyMeanToEventFlow x = bishopCauchyMeanToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x = bishopCauchyMeanFromEventFlow (bishopCauchyMeanToEventFlow x) :=
        (bishopCauchyMean_round_trip x).symm
      _ = bishopCauchyMeanFromEventFlow (bishopCauchyMeanToEventFlow y) :=
        congrArg bishopCauchyMeanFromEventFlow hxy
      _ = some y := bishopCauchyMean_round_trip y
  exact Option.some.inj hsome

private theorem bishopCauchyMean_field_faithful :
    ∀ x y : BishopCauchyMeanUp, bishopCauchyMeanFields x = bishopCauchyMeanFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 D1 W1 R1 A1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 D2 W2 R2 A2 E2 H2 C2 P2 N2 =>
          injection hfields with hS tail0
          injection tail0 with hD tail1
          injection tail1 with hW tail2
          injection tail2 with hR tail3
          injection tail3 with hA tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hS
          subst hD
          subst hW
          subst hR
          subst hA
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance bishopCauchyMeanBHistCarrier : BHistCarrier BishopCauchyMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyMeanToEventFlow
  fromEventFlow := bishopCauchyMeanFromEventFlow

instance bishopCauchyMeanChapterTasteGate : ChapterTasteGate BishopCauchyMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCauchyMeanFromEventFlow (bishopCauchyMeanToEventFlow x) = some x
    exact bishopCauchyMean_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCauchyMeanToEventFlow_injective heq)

instance bishopCauchyMeanFieldFaithful : FieldFaithful BishopCauchyMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCauchyMeanFields
  field_faithful := bishopCauchyMean_field_faithful

instance bishopCauchyMeanNontrivial : Nontrivial BishopCauchyMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCauchyMeanUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopCauchyMeanUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopCauchyMeanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyMeanChapterTasteGate

theorem BishopCauchyMeanTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopCauchyMeanDecodeBHist (bishopCauchyMeanEncodeBHist h) = h) ∧
      (∀ x : BishopCauchyMeanUp,
        bishopCauchyMeanFromEventFlow (bishopCauchyMeanToEventFlow x) = some x) ∧
        (∀ x y : BishopCauchyMeanUp,
          bishopCauchyMeanToEventFlow x = bishopCauchyMeanToEventFlow y → x = y) ∧
          bishopCauchyMeanEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopCauchyMeanTasteGate_single_carrier_alignment_decode,
      bishopCauchyMean_round_trip,
      fun _ _ heq => bishopCauchyMeanToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BishopCauchyMeanUp
