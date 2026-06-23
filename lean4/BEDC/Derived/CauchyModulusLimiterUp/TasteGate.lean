import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusLimiterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusLimiterUp : Type where
  | mk (M L T W R D H C P N : BHist) : CauchyModulusLimiterUp
  deriving DecidableEq

def cauchyModulusLimiterEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusLimiterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusLimiterEncodeBHist h

def cauchyModulusLimiterDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusLimiterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusLimiterDecodeBHist tail)

private theorem CauchyModulusLimiterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyModulusLimiterDecodeBHist
        (cauchyModulusLimiterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusLimiterToEventFlow : CauchyModulusLimiterUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusLimiterUp.mk M L T W R D H C P N =>
      [cauchyModulusLimiterEncodeBHist M,
        cauchyModulusLimiterEncodeBHist L,
        cauchyModulusLimiterEncodeBHist T,
        cauchyModulusLimiterEncodeBHist W,
        cauchyModulusLimiterEncodeBHist R,
        cauchyModulusLimiterEncodeBHist D,
        cauchyModulusLimiterEncodeBHist H,
        cauchyModulusLimiterEncodeBHist C,
        cauchyModulusLimiterEncodeBHist P,
        cauchyModulusLimiterEncodeBHist N]

def cauchyModulusLimiterFromEventFlow : EventFlow -> Option CauchyModulusLimiterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchyModulusLimiterUp.mk
                                                  (cauchyModulusLimiterDecodeBHist M)
                                                  (cauchyModulusLimiterDecodeBHist L)
                                                  (cauchyModulusLimiterDecodeBHist T)
                                                  (cauchyModulusLimiterDecodeBHist W)
                                                  (cauchyModulusLimiterDecodeBHist R)
                                                  (cauchyModulusLimiterDecodeBHist D)
                                                  (cauchyModulusLimiterDecodeBHist H)
                                                  (cauchyModulusLimiterDecodeBHist C)
                                                  (cauchyModulusLimiterDecodeBHist P)
                                                  (cauchyModulusLimiterDecodeBHist N))
                                          | _ :: _ => none

private theorem CauchyModulusLimiterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyModulusLimiterUp,
      cauchyModulusLimiterFromEventFlow
        (cauchyModulusLimiterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M L T W R D H C P N =>
      change
        some
          (CauchyModulusLimiterUp.mk
            (cauchyModulusLimiterDecodeBHist (cauchyModulusLimiterEncodeBHist M))
            (cauchyModulusLimiterDecodeBHist (cauchyModulusLimiterEncodeBHist L))
            (cauchyModulusLimiterDecodeBHist (cauchyModulusLimiterEncodeBHist T))
            (cauchyModulusLimiterDecodeBHist (cauchyModulusLimiterEncodeBHist W))
            (cauchyModulusLimiterDecodeBHist (cauchyModulusLimiterEncodeBHist R))
            (cauchyModulusLimiterDecodeBHist (cauchyModulusLimiterEncodeBHist D))
            (cauchyModulusLimiterDecodeBHist (cauchyModulusLimiterEncodeBHist H))
            (cauchyModulusLimiterDecodeBHist (cauchyModulusLimiterEncodeBHist C))
            (cauchyModulusLimiterDecodeBHist (cauchyModulusLimiterEncodeBHist P))
            (cauchyModulusLimiterDecodeBHist (cauchyModulusLimiterEncodeBHist N))) =
          some (CauchyModulusLimiterUp.mk M L T W R D H C P N)
      rw [CauchyModulusLimiterTasteGate_single_carrier_alignment_decode M,
        CauchyModulusLimiterTasteGate_single_carrier_alignment_decode L,
        CauchyModulusLimiterTasteGate_single_carrier_alignment_decode T,
        CauchyModulusLimiterTasteGate_single_carrier_alignment_decode W,
        CauchyModulusLimiterTasteGate_single_carrier_alignment_decode R,
        CauchyModulusLimiterTasteGate_single_carrier_alignment_decode D,
        CauchyModulusLimiterTasteGate_single_carrier_alignment_decode H,
        CauchyModulusLimiterTasteGate_single_carrier_alignment_decode C,
        CauchyModulusLimiterTasteGate_single_carrier_alignment_decode P,
        CauchyModulusLimiterTasteGate_single_carrier_alignment_decode N]

private theorem CauchyModulusLimiterTasteGate_single_carrier_alignment_injective
    {x y : CauchyModulusLimiterUp} :
    cauchyModulusLimiterToEventFlow x =
      cauchyModulusLimiterToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusLimiterFromEventFlow (cauchyModulusLimiterToEventFlow x) =
        cauchyModulusLimiterFromEventFlow (cauchyModulusLimiterToEventFlow y) :=
    congrArg cauchyModulusLimiterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyModulusLimiterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyModulusLimiterTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyModulusLimiterBHistCarrier :
    BHistCarrier CauchyModulusLimiterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusLimiterToEventFlow
  fromEventFlow := cauchyModulusLimiterFromEventFlow

instance cauchyModulusLimiterChapterTasteGate :
    ChapterTasteGate CauchyModulusLimiterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusLimiterFromEventFlow (cauchyModulusLimiterToEventFlow x) =
      some x
    exact CauchyModulusLimiterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyModulusLimiterTasteGate_single_carrier_alignment_injective heq)

instance cauchyModulusLimiterNontrivial : Nontrivial CauchyModulusLimiterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyModulusLimiterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyModulusLimiterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyModulusLimiterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusLimiterChapterTasteGate

theorem CauchyModulusLimiterTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyModulusLimiterUp) ∧
      Nonempty (ChapterTasteGate CauchyModulusLimiterUp) ∧
        Nonempty (Nontrivial CauchyModulusLimiterUp) ∧
          cauchyModulusLimiterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨cauchyModulusLimiterBHistCarrier⟩,
      ⟨cauchyModulusLimiterChapterTasteGate⟩,
      ⟨cauchyModulusLimiterNontrivial⟩,
      rfl⟩

end BEDC.Derived.CauchyModulusLimiterUp
