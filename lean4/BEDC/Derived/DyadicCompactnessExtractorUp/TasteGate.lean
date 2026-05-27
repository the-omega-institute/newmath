import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCompactnessExtractorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCompactnessExtractorUp : Type where
  | mk (K M T R F L U H C P N : BHist) : DyadicCompactnessExtractorUp
  deriving DecidableEq

def dyadicCompactnessExtractorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCompactnessExtractorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCompactnessExtractorEncodeBHist h

def dyadicCompactnessExtractorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCompactnessExtractorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCompactnessExtractorDecodeBHist tail)

private theorem DyadicCompactnessExtractorTasteGate_decode :
    forall h : BHist,
      dyadicCompactnessExtractorDecodeBHist
        (dyadicCompactnessExtractorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicCompactnessExtractorFields : DyadicCompactnessExtractorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCompactnessExtractorUp.mk K M T R F L U H C P N =>
      [K, M, T, R, F, L, U, H, C, P, N]

def dyadicCompactnessExtractorToEventFlow : DyadicCompactnessExtractorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicCompactnessExtractorFields x).map dyadicCompactnessExtractorEncodeBHist

def dyadicCompactnessExtractorFromEventFlow :
    EventFlow -> Option DyadicCompactnessExtractorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | F :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | U :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (DyadicCompactnessExtractorUp.mk
                                                      (dyadicCompactnessExtractorDecodeBHist K)
                                                      (dyadicCompactnessExtractorDecodeBHist M)
                                                      (dyadicCompactnessExtractorDecodeBHist T)
                                                      (dyadicCompactnessExtractorDecodeBHist R)
                                                      (dyadicCompactnessExtractorDecodeBHist F)
                                                      (dyadicCompactnessExtractorDecodeBHist L)
                                                      (dyadicCompactnessExtractorDecodeBHist U)
                                                      (dyadicCompactnessExtractorDecodeBHist H)
                                                      (dyadicCompactnessExtractorDecodeBHist C)
                                                      (dyadicCompactnessExtractorDecodeBHist P)
                                                      (dyadicCompactnessExtractorDecodeBHist N))
                                              | _ :: _ => none

private theorem dyadicCompactnessExtractor_round_trip :
    forall x : DyadicCompactnessExtractorUp,
      dyadicCompactnessExtractorFromEventFlow
        (dyadicCompactnessExtractorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K M T R F L U H C P N =>
      change
        some
          (DyadicCompactnessExtractorUp.mk
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist K))
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist M))
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist T))
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist R))
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist F))
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist L))
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist U))
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist H))
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist C))
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist P))
            (dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist N))) =
          some (DyadicCompactnessExtractorUp.mk K M T R F L U H C P N)
      rw [DyadicCompactnessExtractorTasteGate_decode K,
        DyadicCompactnessExtractorTasteGate_decode M,
        DyadicCompactnessExtractorTasteGate_decode T,
        DyadicCompactnessExtractorTasteGate_decode R,
        DyadicCompactnessExtractorTasteGate_decode F,
        DyadicCompactnessExtractorTasteGate_decode L,
        DyadicCompactnessExtractorTasteGate_decode U,
        DyadicCompactnessExtractorTasteGate_decode H,
        DyadicCompactnessExtractorTasteGate_decode C,
        DyadicCompactnessExtractorTasteGate_decode P,
        DyadicCompactnessExtractorTasteGate_decode N]

private theorem dyadicCompactnessExtractorToEventFlow_injective
    {x y : DyadicCompactnessExtractorUp} :
    dyadicCompactnessExtractorToEventFlow x =
      dyadicCompactnessExtractorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCompactnessExtractorFromEventFlow
          (dyadicCompactnessExtractorToEventFlow x) =
        dyadicCompactnessExtractorFromEventFlow
          (dyadicCompactnessExtractorToEventFlow y) :=
    congrArg dyadicCompactnessExtractorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicCompactnessExtractor_round_trip x).symm
      (Eq.trans hread (dyadicCompactnessExtractor_round_trip y)))

private theorem dyadicCompactnessExtractor_fields_faithful :
    forall x y : DyadicCompactnessExtractorUp,
      dyadicCompactnessExtractorFields x = dyadicCompactnessExtractorFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 M1 T1 R1 F1 L1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 M2 T2 R2 F2 L2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicCompactnessExtractorBHistCarrier :
    BHistCarrier DyadicCompactnessExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCompactnessExtractorToEventFlow
  fromEventFlow := dyadicCompactnessExtractorFromEventFlow

instance dyadicCompactnessExtractorChapterTasteGate :
    ChapterTasteGate DyadicCompactnessExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicCompactnessExtractorFromEventFlow
        (dyadicCompactnessExtractorToEventFlow x) = some x
    exact dyadicCompactnessExtractor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicCompactnessExtractorToEventFlow_injective heq)

instance dyadicCompactnessExtractorFieldFaithful :
    FieldFaithful DyadicCompactnessExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicCompactnessExtractorFields
  field_faithful := dyadicCompactnessExtractor_fields_faithful

instance dyadicCompactnessExtractorNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicCompactnessExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicCompactnessExtractorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicCompactnessExtractorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicCompactnessExtractorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicCompactnessExtractorChapterTasteGate

theorem DyadicCompactnessExtractorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicCompactnessExtractorUp) ∧
      Nonempty (FieldFaithful DyadicCompactnessExtractorUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DyadicCompactnessExtractorUp) ∧
          (forall h : BHist,
            dyadicCompactnessExtractorDecodeBHist
              (dyadicCompactnessExtractorEncodeBHist h) = h) ∧
            (forall x : DyadicCompactnessExtractorUp,
              dyadicCompactnessExtractorFromEventFlow
                (dyadicCompactnessExtractorToEventFlow x) = some x) ∧
              (forall x y : DyadicCompactnessExtractorUp,
                dyadicCompactnessExtractorToEventFlow x =
                  dyadicCompactnessExtractorToEventFlow y -> x = y) ∧
                dyadicCompactnessExtractorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨dyadicCompactnessExtractorChapterTasteGate⟩,
      ⟨dyadicCompactnessExtractorFieldFaithful⟩,
      ⟨dyadicCompactnessExtractorNontrivial⟩,
      DyadicCompactnessExtractorTasteGate_decode,
      dyadicCompactnessExtractor_round_trip,
      (fun _ _ heq => dyadicCompactnessExtractorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicCompactnessExtractorUp
