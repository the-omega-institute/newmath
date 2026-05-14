import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubstitutionAuditWindowRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubstitutionAuditWindowRouteUp : Type where
  | mk (T D L M C G B H R P N : BHist) : SubstitutionAuditWindowRouteUp
  deriving DecidableEq

def substitutionAuditWindowRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: substitutionAuditWindowRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: substitutionAuditWindowRouteEncodeBHist h

def substitutionAuditWindowRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (substitutionAuditWindowRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (substitutionAuditWindowRouteDecodeBHist tail)

private theorem substitutionAuditWindowRouteDecode_encode_bhist :
    ∀ h : BHist,
      substitutionAuditWindowRouteDecodeBHist
        (substitutionAuditWindowRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem substitutionAuditWindowRoute_mk_congr
    {T T' D D' L L' M M' C C' G G' B B' H H' R R' P P' N N' : BHist}
    (hT : T' = T)
    (hD : D' = D)
    (hL : L' = L)
    (hM : M' = M)
    (hC : C' = C)
    (hG : G' = G)
    (hB : B' = B)
    (hH : H' = H)
    (hR : R' = R)
    (hP : P' = P)
    (hN : N' = N) :
    SubstitutionAuditWindowRouteUp.mk T' D' L' M' C' G' B' H' R' P' N' =
      SubstitutionAuditWindowRouteUp.mk T D L M C G B H R P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hT
  cases hD
  cases hL
  cases hM
  cases hC
  cases hG
  cases hB
  cases hH
  cases hR
  cases hP
  cases hN
  rfl

def substitutionAuditWindowRouteToEventFlow :
    SubstitutionAuditWindowRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubstitutionAuditWindowRouteUp.mk T D L M C G B H R P N =>
      [[BMark.b0],
        substitutionAuditWindowRouteEncodeBHist T,
        [BMark.b1, BMark.b0],
        substitutionAuditWindowRouteEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditWindowRouteEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditWindowRouteEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditWindowRouteEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditWindowRouteEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditWindowRouteEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        substitutionAuditWindowRouteEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        substitutionAuditWindowRouteEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditWindowRouteEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditWindowRouteEncodeBHist N]

def substitutionAuditWindowRouteFromEventFlow :
    EventFlow → Option SubstitutionAuditWindowRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | M :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | G :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | B :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | R :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (SubstitutionAuditWindowRouteUp.mk
                                                                                                  (substitutionAuditWindowRouteDecodeBHist T)
                                                                                                  (substitutionAuditWindowRouteDecodeBHist D)
                                                                                                  (substitutionAuditWindowRouteDecodeBHist L)
                                                                                                  (substitutionAuditWindowRouteDecodeBHist M)
                                                                                                  (substitutionAuditWindowRouteDecodeBHist C)
                                                                                                  (substitutionAuditWindowRouteDecodeBHist G)
                                                                                                  (substitutionAuditWindowRouteDecodeBHist B)
                                                                                                  (substitutionAuditWindowRouteDecodeBHist H)
                                                                                                  (substitutionAuditWindowRouteDecodeBHist R)
                                                                                                  (substitutionAuditWindowRouteDecodeBHist P)
                                                                                                  (substitutionAuditWindowRouteDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem substitutionAuditWindowRoute_round_trip :
    ∀ x : SubstitutionAuditWindowRouteUp,
      substitutionAuditWindowRouteFromEventFlow
        (substitutionAuditWindowRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T D L M C G B H R P N =>
      change
        some
          (SubstitutionAuditWindowRouteUp.mk
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist T))
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist D))
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist L))
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist M))
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist C))
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist G))
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist B))
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist H))
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist R))
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist P))
            (substitutionAuditWindowRouteDecodeBHist
              (substitutionAuditWindowRouteEncodeBHist N))) =
          some (SubstitutionAuditWindowRouteUp.mk T D L M C G B H R P N)
      exact
        congrArg some
          (substitutionAuditWindowRoute_mk_congr
            (substitutionAuditWindowRouteDecode_encode_bhist T)
            (substitutionAuditWindowRouteDecode_encode_bhist D)
            (substitutionAuditWindowRouteDecode_encode_bhist L)
            (substitutionAuditWindowRouteDecode_encode_bhist M)
            (substitutionAuditWindowRouteDecode_encode_bhist C)
            (substitutionAuditWindowRouteDecode_encode_bhist G)
            (substitutionAuditWindowRouteDecode_encode_bhist B)
            (substitutionAuditWindowRouteDecode_encode_bhist H)
            (substitutionAuditWindowRouteDecode_encode_bhist R)
            (substitutionAuditWindowRouteDecode_encode_bhist P)
            (substitutionAuditWindowRouteDecode_encode_bhist N))

private theorem substitutionAuditWindowRouteToEventFlow_injective
    {x y : SubstitutionAuditWindowRouteUp} :
    substitutionAuditWindowRouteToEventFlow x =
      substitutionAuditWindowRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      substitutionAuditWindowRouteFromEventFlow
          (substitutionAuditWindowRouteToEventFlow x) =
        substitutionAuditWindowRouteFromEventFlow
          (substitutionAuditWindowRouteToEventFlow y) :=
    congrArg substitutionAuditWindowRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (substitutionAuditWindowRoute_round_trip x).symm
      (Eq.trans hread (substitutionAuditWindowRoute_round_trip y)))

instance substitutionAuditWindowRouteBHistCarrier :
    BHistCarrier SubstitutionAuditWindowRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := substitutionAuditWindowRouteToEventFlow
  fromEventFlow := substitutionAuditWindowRouteFromEventFlow

instance substitutionAuditWindowRouteChapterTasteGate :
    ChapterTasteGate SubstitutionAuditWindowRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      substitutionAuditWindowRouteFromEventFlow
        (substitutionAuditWindowRouteToEventFlow x) = some x
    exact substitutionAuditWindowRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (substitutionAuditWindowRouteToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SubstitutionAuditWindowRouteUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact substitutionAuditWindowRouteChapterTasteGate

def substitutionAuditWindowRouteFields : SubstitutionAuditWindowRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubstitutionAuditWindowRouteUp.mk T D L M C G B H R P N =>
      [T, D, L, M, C, G, B, H, R, P, N]

instance substitutionAuditWindowRouteFieldFaithful :
    FieldFaithful SubstitutionAuditWindowRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := substitutionAuditWindowRouteFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk T D L M C G B H R P N =>
        cases y with
        | mk T' D' L' M' C' G' B' H' R' P' N' =>
            injection hfields with hT htail0
            injection htail0 with hD htail1
            injection htail1 with hL htail2
            injection htail2 with hM htail3
            injection htail3 with hC htail4
            injection htail4 with hG htail5
            injection htail5 with hB htail6
            injection htail6 with hH htail7
            injection htail7 with hR htail8
            injection htail8 with hP htail9
            injection htail9 with hN _hNil
            cases hT
            cases hD
            cases hL
            cases hM
            cases hC
            cases hG
            cases hB
            cases hH
            cases hR
            cases hP
            cases hN
            rfl

theorem SubstitutionAuditWindowRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      substitutionAuditWindowRouteDecodeBHist
        (substitutionAuditWindowRouteEncodeBHist h) = h) ∧
      (∀ x : SubstitutionAuditWindowRouteUp,
        substitutionAuditWindowRouteFromEventFlow
          (substitutionAuditWindowRouteToEventFlow x) = some x) ∧
        (∀ x y : SubstitutionAuditWindowRouteUp,
          substitutionAuditWindowRouteToEventFlow x =
            substitutionAuditWindowRouteToEventFlow y → x = y) ∧
          substitutionAuditWindowRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact substitutionAuditWindowRouteDecode_encode_bhist
  · constructor
    · exact substitutionAuditWindowRoute_round_trip
    · constructor
      · intro x y heq
        exact substitutionAuditWindowRouteToEventFlow_injective heq
      · rfl

end BEDC.Derived.SubstitutionAuditWindowRouteUp
