import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicTailBallUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicTailBallUp : Type where
  | mk (B D F R H C P N : BHist) : DyadicTailBallUp
  deriving DecidableEq

def dyadicTailBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicTailBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicTailBallEncodeBHist h

def dyadicTailBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicTailBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicTailBallDecodeBHist tail)

theorem DyadicTailBallTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, dyadicTailBallDecodeBHist (dyadicTailBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicTailBallFields : DyadicTailBallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicTailBallUp.mk B D F R H C P N => [B, D, F, R, H, C, P, N]

def dyadicTailBallToEventFlow : DyadicTailBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicTailBallFields x).map dyadicTailBallEncodeBHist

def dyadicTailBallFromEventFlow : EventFlow → Option DyadicTailBallUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | F :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (DyadicTailBallUp.mk
                                          (dyadicTailBallDecodeBHist B)
                                          (dyadicTailBallDecodeBHist D)
                                          (dyadicTailBallDecodeBHist F)
                                          (dyadicTailBallDecodeBHist R)
                                          (dyadicTailBallDecodeBHist H)
                                          (dyadicTailBallDecodeBHist C)
                                          (dyadicTailBallDecodeBHist P)
                                          (dyadicTailBallDecodeBHist N))
                                  | _ :: _ => none

theorem DyadicTailBallTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicTailBallUp,
      dyadicTailBallFromEventFlow (dyadicTailBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B D F R H C P N =>
      change
        some
          (DyadicTailBallUp.mk
            (dyadicTailBallDecodeBHist (dyadicTailBallEncodeBHist B))
            (dyadicTailBallDecodeBHist (dyadicTailBallEncodeBHist D))
            (dyadicTailBallDecodeBHist (dyadicTailBallEncodeBHist F))
            (dyadicTailBallDecodeBHist (dyadicTailBallEncodeBHist R))
            (dyadicTailBallDecodeBHist (dyadicTailBallEncodeBHist H))
            (dyadicTailBallDecodeBHist (dyadicTailBallEncodeBHist C))
            (dyadicTailBallDecodeBHist (dyadicTailBallEncodeBHist P))
            (dyadicTailBallDecodeBHist (dyadicTailBallEncodeBHist N))) =
          some (DyadicTailBallUp.mk B D F R H C P N)
      rw [DyadicTailBallTasteGate_single_carrier_alignment_decode B,
        DyadicTailBallTasteGate_single_carrier_alignment_decode D,
        DyadicTailBallTasteGate_single_carrier_alignment_decode F,
        DyadicTailBallTasteGate_single_carrier_alignment_decode R,
        DyadicTailBallTasteGate_single_carrier_alignment_decode H,
        DyadicTailBallTasteGate_single_carrier_alignment_decode C,
        DyadicTailBallTasteGate_single_carrier_alignment_decode P,
        DyadicTailBallTasteGate_single_carrier_alignment_decode N]

theorem DyadicTailBallTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicTailBallUp} :
    dyadicTailBallToEventFlow x = dyadicTailBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicTailBallFromEventFlow (dyadicTailBallToEventFlow x) =
        dyadicTailBallFromEventFlow (dyadicTailBallToEventFlow y) :=
    congrArg dyadicTailBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicTailBallTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicTailBallTasteGate_single_carrier_alignment_round_trip y)))

theorem DyadicTailBallTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : DyadicTailBallUp, dyadicTailBallFields x = dyadicTailBallFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 D1 F1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 D2 F2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicTailBallBHistCarrier : BHistCarrier DyadicTailBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicTailBallToEventFlow
  fromEventFlow := dyadicTailBallFromEventFlow

instance dyadicTailBallChapterTasteGate : ChapterTasteGate DyadicTailBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (DyadicTailBallTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicTailBallTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicTailBallFieldFaithful : FieldFaithful DyadicTailBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicTailBallFields
  field_faithful := DyadicTailBallTasteGate_single_carrier_alignment_field_faithful

instance dyadicTailBallNontrivial : Nontrivial DyadicTailBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicTailBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicTailBallUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicTailBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicTailBallChapterTasteGate

theorem DyadicTailBallTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicTailBallUp) ∧
      Nonempty (FieldFaithful DyadicTailBallUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DyadicTailBallUp) ∧
          (∀ h : BHist, dyadicTailBallDecodeBHist (dyadicTailBallEncodeBHist h) = h) ∧
            (∀ x : DyadicTailBallUp,
              dyadicTailBallFromEventFlow (dyadicTailBallToEventFlow x) = some x) ∧
              (∀ x y : DyadicTailBallUp,
                dyadicTailBallToEventFlow x = dyadicTailBallToEventFlow y → x = y) ∧
                dyadicTailBallEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨dyadicTailBallChapterTasteGate⟩,
      ⟨dyadicTailBallFieldFaithful⟩,
      ⟨dyadicTailBallNontrivial⟩,
      DyadicTailBallTasteGate_single_carrier_alignment_decode,
      DyadicTailBallTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DyadicTailBallTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicTailBallUp.TasteGate

namespace BEDC.Derived.DyadicTailBallUp

theorem DyadicTailBallTasteGate_single_carrier_alignment :
    Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.DyadicTailBallUp) ∧
      Nonempty (BEDC.Meta.TasteGate.FieldFaithful TasteGate.DyadicTailBallUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial TasteGate.DyadicTailBallUp) ∧
          (∀ h : BEDC.FKernel.Hist.BHist,
            TasteGate.dyadicTailBallDecodeBHist (TasteGate.dyadicTailBallEncodeBHist h) = h) ∧
            (∀ x : TasteGate.DyadicTailBallUp,
              TasteGate.dyadicTailBallFromEventFlow (TasteGate.dyadicTailBallToEventFlow x) =
                some x) ∧
              (∀ x y : TasteGate.DyadicTailBallUp,
                TasteGate.dyadicTailBallToEventFlow x = TasteGate.dyadicTailBallToEventFlow y →
                  x = y) ∧
                TasteGate.dyadicTailBallEncodeBHist BEDC.FKernel.Hist.BHist.Empty =
                  ([] : BEDC.GroundCompiler.EventFlow.RawEvent) := by
  exact TasteGate.DyadicTailBallTasteGate_single_carrier_alignment

end BEDC.Derived.DyadicTailBallUp
