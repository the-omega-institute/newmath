import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductTheoremUp : Type where
  | mk (A B S T D L R E H C P N : BHist) : CauchyProductTheoremUp
  deriving DecidableEq

def cauchyProductTheoremEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductTheoremEncodeBHist h

def cauchyProductTheoremDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductTheoremDecodeBHist tail)

private theorem CauchyProductTheoremTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductTheoremFields : CauchyProductTheoremUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductTheoremUp.mk A B S T D L R E H C P N =>
      [A, B, S, T, D, L, R, E, H, C, P, N]

def cauchyProductTheoremToEventFlow : CauchyProductTheoremUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyProductTheoremFields x).map cauchyProductTheoremEncodeBHist

private def cauchyProductTheoremEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, event :: _ => event
  | Nat.succ n, _ :: rest => cauchyProductTheoremEventAt n rest
  | _, [] => []

def cauchyProductTheoremFromEventFlow
    (flow : EventFlow) : Option CauchyProductTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyProductTheoremUp.mk
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 0 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 1 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 2 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 3 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 4 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 5 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 6 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 7 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 8 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 9 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 10 flow))
      (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEventAt 11 flow)))

private theorem CauchyProductTheoremTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyProductTheoremUp,
      cauchyProductTheoremFromEventFlow (cauchyProductTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B S T D L R E H C P N =>
      change
        some
          (CauchyProductTheoremUp.mk
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist A))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist B))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist S))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist T))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist D))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist L))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist R))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist E))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist H))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist C))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist P))
            (cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist N))) =
          some (CauchyProductTheoremUp.mk A B S T D L R E H C P N)
      rw [CauchyProductTheoremTasteGate_single_carrier_alignment_decode A,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode B,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode S,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode T,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode D,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode L,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode R,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode E,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode H,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode C,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode P,
        CauchyProductTheoremTasteGate_single_carrier_alignment_decode N]

private theorem CauchyProductTheoremTasteGate_single_carrier_alignment_injective
    {x y : CauchyProductTheoremUp} :
    cauchyProductTheoremToEventFlow x = cauchyProductTheoremToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductTheoremFromEventFlow (cauchyProductTheoremToEventFlow x) =
        cauchyProductTheoremFromEventFlow (cauchyProductTheoremToEventFlow y) :=
    congrArg cauchyProductTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyProductTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyProductTheoremTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyProductTheoremTasteGate_single_carrier_alignment_fields :
    forall x y : CauchyProductTheoremUp,
      cauchyProductTheoremFields x = cauchyProductTheoremFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 B1 S1 T1 D1 L1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 B2 S2 T2 D2 L2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyProductTheoremBHistCarrier :
    BHistCarrier CauchyProductTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductTheoremToEventFlow
  fromEventFlow := cauchyProductTheoremFromEventFlow

instance cauchyProductTheoremChapterTasteGate :
    ChapterTasteGate CauchyProductTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyProductTheoremFromEventFlow (cauchyProductTheoremToEventFlow x) = some x
    exact CauchyProductTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyProductTheoremTasteGate_single_carrier_alignment_injective heq)

instance cauchyProductTheoremFieldFaithful :
    FieldFaithful CauchyProductTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyProductTheoremFields
  field_faithful := CauchyProductTheoremTasteGate_single_carrier_alignment_fields

instance cauchyProductTheoremNontrivial : Nontrivial CauchyProductTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyProductTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CauchyProductTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyProductTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyProductTheoremChapterTasteGate

theorem CauchyProductTheoremTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyProductTheoremUp) /\
      Nonempty (FieldFaithful CauchyProductTheoremUp) /\
        Nonempty (Nontrivial CauchyProductTheoremUp) /\
          (forall h : BHist,
            cauchyProductTheoremDecodeBHist (cauchyProductTheoremEncodeBHist h) = h) /\
            (forall x : CauchyProductTheoremUp,
              cauchyProductTheoremFromEventFlow
                (cauchyProductTheoremToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyProductTheoremChapterTasteGate⟩,
      ⟨cauchyProductTheoremFieldFaithful⟩,
      ⟨cauchyProductTheoremNontrivial⟩,
      CauchyProductTheoremTasteGate_single_carrier_alignment_decode,
      CauchyProductTheoremTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.CauchyProductTheoremUp
