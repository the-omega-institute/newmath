import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CookCompileFrontierWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CookCompileFrontierWitnessUp : Type where
  | mk : (s q a o h c p n : BHist) → CookCompileFrontierWitnessUp
  deriving DecidableEq

def cookCompileFrontierWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cookCompileFrontierWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cookCompileFrontierWitnessEncodeBHist h

def cookCompileFrontierWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cookCompileFrontierWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cookCompileFrontierWitnessDecodeBHist tail)

private theorem cookCompileFrontierWitnessDecode_encode_bhist :
    ∀ h : BHist,
      cookCompileFrontierWitnessDecodeBHist
        (cookCompileFrontierWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cookCompileFrontierWitnessToEventFlow : CookCompileFrontierWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CookCompileFrontierWitnessUp.mk s q a o h c p n =>
      [[BMark.b0],
        cookCompileFrontierWitnessEncodeBHist s,
        [BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist q,
        [BMark.b1, BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist a,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist o,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cookCompileFrontierWitnessEncodeBHist n]

def cookCompileFrontierWitnessFromEventFlow :
    EventFlow → Option CookCompileFrontierWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | s :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | a :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | o :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | h :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | c :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | p :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | n :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (CookCompileFrontierWitnessUp.mk
                                                                          (cookCompileFrontierWitnessDecodeBHist s)
                                                                          (cookCompileFrontierWitnessDecodeBHist q)
                                                                          (cookCompileFrontierWitnessDecodeBHist a)
                                                                          (cookCompileFrontierWitnessDecodeBHist o)
                                                                          (cookCompileFrontierWitnessDecodeBHist h)
                                                                          (cookCompileFrontierWitnessDecodeBHist c)
                                                                          (cookCompileFrontierWitnessDecodeBHist p)
                                                                          (cookCompileFrontierWitnessDecodeBHist n))
                                                                  | _ :: _ => none

private theorem cookCompileFrontierWitness_round_trip :
    ∀ x : CookCompileFrontierWitnessUp,
      cookCompileFrontierWitnessFromEventFlow
        (cookCompileFrontierWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk s q a o h c p n =>
      change
        some
          (CookCompileFrontierWitnessUp.mk
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist s))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist q))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist a))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist o))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist h))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist c))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist p))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist n))) =
          some (CookCompileFrontierWitnessUp.mk s q a o h c p n)
      rw [cookCompileFrontierWitnessDecode_encode_bhist s,
        cookCompileFrontierWitnessDecode_encode_bhist q,
        cookCompileFrontierWitnessDecode_encode_bhist a,
        cookCompileFrontierWitnessDecode_encode_bhist o,
        cookCompileFrontierWitnessDecode_encode_bhist h,
        cookCompileFrontierWitnessDecode_encode_bhist c,
        cookCompileFrontierWitnessDecode_encode_bhist p,
        cookCompileFrontierWitnessDecode_encode_bhist n]

private theorem cookCompileFrontierWitnessToEventFlow_injective
    {x y : CookCompileFrontierWitnessUp} :
    cookCompileFrontierWitnessToEventFlow x =
      cookCompileFrontierWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cookCompileFrontierWitnessFromEventFlow (cookCompileFrontierWitnessToEventFlow x) =
        cookCompileFrontierWitnessFromEventFlow (cookCompileFrontierWitnessToEventFlow y) :=
    congrArg cookCompileFrontierWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cookCompileFrontierWitness_round_trip x).symm
      (Eq.trans hread (cookCompileFrontierWitness_round_trip y)))

instance cookCompileFrontierWitnessBHistCarrier :
    BHistCarrier CookCompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cookCompileFrontierWitnessToEventFlow
  fromEventFlow := cookCompileFrontierWitnessFromEventFlow

instance cookCompileFrontierWitnessChapterTasteGate :
    ChapterTasteGate CookCompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cookCompileFrontierWitnessFromEventFlow
        (cookCompileFrontierWitnessToEventFlow x) = some x
    exact cookCompileFrontierWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cookCompileFrontierWitnessToEventFlow_injective heq)

instance cookCompileFrontierWitnessFieldFaithful :
    FieldFaithful CookCompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CookCompileFrontierWitnessUp.mk s q a o h c p n => [s, q, a, o, h, c, p, n]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk s1 q1 a1 o1 h1 c1 p1 n1 =>
        cases y with
        | mk s2 q2 a2 o2 h2 c2 p2 n2 =>
            cases hfields
            rfl

instance cookCompileFrontierWitnessNontrivial :
    Nontrivial CookCompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CookCompileFrontierWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CookCompileFrontierWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CookCompileFrontierWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cookCompileFrontierWitnessChapterTasteGate

theorem CookCompileFrontierWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cookCompileFrontierWitnessDecodeBHist
        (cookCompileFrontierWitnessEncodeBHist h) = h) ∧
      (∀ x : CookCompileFrontierWitnessUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        (∀ x y : CookCompileFrontierWitnessUp,
          BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y -> x = y) ∧
          cookCompileFrontierWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cookCompileFrontierWitnessDecode_encode_bhist
  · constructor
    · intro x
      change
        cookCompileFrontierWitnessFromEventFlow
          (cookCompileFrontierWitnessToEventFlow x) = some x
      exact cookCompileFrontierWitness_round_trip x
    · constructor
      · intro x y heq
        exact cookCompileFrontierWitnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.CookCompileFrontierWitnessUp
