import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistNonaSequenceNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistNonaSequenceNameCertUp : Type where
  | mk :
      (head first second third fourth fifth sixth seventh tail : BHist) →
      BHistNonaSequenceNameCertUp
  deriving DecidableEq

def bHistNonaSequenceNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistNonaSequenceNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistNonaSequenceNameCertEncodeBHist h

def bHistNonaSequenceNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistNonaSequenceNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistNonaSequenceNameCertDecodeBHist tail)

private theorem bHistNonaSequenceNameCertDecode_encode_bhist :
    ∀ h : BHist,
      bHistNonaSequenceNameCertDecodeBHist
        (bHistNonaSequenceNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bHistNonaSequenceNameCertToEventFlow :
    BHistNonaSequenceNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistNonaSequenceNameCertUp.mk head first second third fourth fifth sixth seventh tail =>
      [[BMark.b0],
        bHistNonaSequenceNameCertEncodeBHist head,
        [BMark.b1, BMark.b0],
        bHistNonaSequenceNameCertEncodeBHist first,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistNonaSequenceNameCertEncodeBHist second,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistNonaSequenceNameCertEncodeBHist third,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistNonaSequenceNameCertEncodeBHist fourth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistNonaSequenceNameCertEncodeBHist fifth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistNonaSequenceNameCertEncodeBHist sixth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistNonaSequenceNameCertEncodeBHist seventh,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bHistNonaSequenceNameCertEncodeBHist tail]

def bHistNonaSequenceNameCertFromEventFlow :
    EventFlow → Option BHistNonaSequenceNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | head :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | first :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | second :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | third :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | fourth :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | fifth :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | sixth :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | seventh :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | tail :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (BHistNonaSequenceNameCertUp.mk
                                                                                  (bHistNonaSequenceNameCertDecodeBHist head)
                                                                                  (bHistNonaSequenceNameCertDecodeBHist first)
                                                                                  (bHistNonaSequenceNameCertDecodeBHist second)
                                                                                  (bHistNonaSequenceNameCertDecodeBHist third)
                                                                                  (bHistNonaSequenceNameCertDecodeBHist fourth)
                                                                                  (bHistNonaSequenceNameCertDecodeBHist fifth)
                                                                                  (bHistNonaSequenceNameCertDecodeBHist sixth)
                                                                                  (bHistNonaSequenceNameCertDecodeBHist seventh)
                                                                                  (bHistNonaSequenceNameCertDecodeBHist tail))
                                                                          | _ :: _ => none

private theorem bHistNonaSequenceNameCert_round_trip :
    ∀ x : BHistNonaSequenceNameCertUp,
      bHistNonaSequenceNameCertFromEventFlow
        (bHistNonaSequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk head first second third fourth fifth sixth seventh tail =>
      change
        some
          (BHistNonaSequenceNameCertUp.mk
            (bHistNonaSequenceNameCertDecodeBHist
              (bHistNonaSequenceNameCertEncodeBHist head))
            (bHistNonaSequenceNameCertDecodeBHist
              (bHistNonaSequenceNameCertEncodeBHist first))
            (bHistNonaSequenceNameCertDecodeBHist
              (bHistNonaSequenceNameCertEncodeBHist second))
            (bHistNonaSequenceNameCertDecodeBHist
              (bHistNonaSequenceNameCertEncodeBHist third))
            (bHistNonaSequenceNameCertDecodeBHist
              (bHistNonaSequenceNameCertEncodeBHist fourth))
            (bHistNonaSequenceNameCertDecodeBHist
              (bHistNonaSequenceNameCertEncodeBHist fifth))
            (bHistNonaSequenceNameCertDecodeBHist
              (bHistNonaSequenceNameCertEncodeBHist sixth))
            (bHistNonaSequenceNameCertDecodeBHist
              (bHistNonaSequenceNameCertEncodeBHist seventh))
            (bHistNonaSequenceNameCertDecodeBHist
              (bHistNonaSequenceNameCertEncodeBHist tail))) =
          some
            (BHistNonaSequenceNameCertUp.mk head first second third fourth fifth sixth
              seventh tail)
      rw [bHistNonaSequenceNameCertDecode_encode_bhist head,
        bHistNonaSequenceNameCertDecode_encode_bhist first,
        bHistNonaSequenceNameCertDecode_encode_bhist second,
        bHistNonaSequenceNameCertDecode_encode_bhist third,
        bHistNonaSequenceNameCertDecode_encode_bhist fourth,
        bHistNonaSequenceNameCertDecode_encode_bhist fifth,
        bHistNonaSequenceNameCertDecode_encode_bhist sixth,
        bHistNonaSequenceNameCertDecode_encode_bhist seventh,
        bHistNonaSequenceNameCertDecode_encode_bhist tail]

private theorem bHistNonaSequenceNameCertToEventFlow_injective
    {x y : BHistNonaSequenceNameCertUp} :
    bHistNonaSequenceNameCertToEventFlow x =
      bHistNonaSequenceNameCertToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistNonaSequenceNameCertFromEventFlow
          (bHistNonaSequenceNameCertToEventFlow x) =
        bHistNonaSequenceNameCertFromEventFlow
          (bHistNonaSequenceNameCertToEventFlow y) :=
    congrArg bHistNonaSequenceNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bHistNonaSequenceNameCert_round_trip x).symm
      (Eq.trans hread (bHistNonaSequenceNameCert_round_trip y)))

instance bHistNonaSequenceNameCertBHistCarrier :
    BHistCarrier BHistNonaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistNonaSequenceNameCertToEventFlow
  fromEventFlow := bHistNonaSequenceNameCertFromEventFlow

instance bHistNonaSequenceNameCertChapterTasteGate :
    ChapterTasteGate BHistNonaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistNonaSequenceNameCertFromEventFlow
        (bHistNonaSequenceNameCertToEventFlow x) = some x
    exact bHistNonaSequenceNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistNonaSequenceNameCertToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BHistNonaSequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bHistNonaSequenceNameCertChapterTasteGate

instance bHistNonaSequenceNameCertFieldFaithful :
    FieldFaithful BHistNonaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BHistNonaSequenceNameCertUp.mk head first second third fourth fifth sixth seventh tail =>
        [head, first, second, third, fourth, fifth, sixth, seventh, tail]
  field_faithful := by
    intro x y h
    cases x with
    | mk head₁ first₁ second₁ third₁ fourth₁ fifth₁ sixth₁ seventh₁ tail₁ =>
        cases y with
        | mk head₂ first₂ second₂ third₂ fourth₂ fifth₂ sixth₂ seventh₂ tail₂ =>
            injection h with hHead t1
            injection t1 with hFirst t2
            injection t2 with hSecond t3
            injection t3 with hThird t4
            injection t4 with hFourth t5
            injection t5 with hFifth t6
            injection t6 with hSixth t7
            injection t7 with hSeventh t8
            injection t8 with hTail _
            cases hHead
            cases hFirst
            cases hSecond
            cases hThird
            cases hFourth
            cases hFifth
            cases hSixth
            cases hSeventh
            cases hTail
            rfl

instance bHistNonaSequenceNameCertNontrivial :
    Nontrivial BHistNonaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistNonaSequenceNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BHistNonaSequenceNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BHistNonaSequenceNameCert_single_carrier_alignment :
    forall x : BHistNonaSequenceNameCertUp,
      bHistNonaSequenceNameCertFromEventFlow
        (bHistNonaSequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  exact bHistNonaSequenceNameCert_round_trip

end BEDC.Derived.BHistNonaSequenceNameCertUp
