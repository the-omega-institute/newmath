import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeakOmniscienceBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeakOmniscienceBoundaryUp : Type where
  | mk (R E K S Q F H C P N : BHist) : WeakOmniscienceBoundaryUp
  deriving DecidableEq

private def weakOmniscienceBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weakOmniscienceBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weakOmniscienceBoundaryEncodeBHist h

private def weakOmniscienceBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weakOmniscienceBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weakOmniscienceBoundaryDecodeBHist tail)

private theorem weakOmniscienceBoundaryDecode_encode_bhist :
    ∀ h : BHist, weakOmniscienceBoundaryDecodeBHist
      (weakOmniscienceBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem weakOmniscienceBoundary_mk_congr
    {R R' E E' K K' S S' Q Q' F F' H H' C C' P P' N N' : BHist}
    (hR : R' = R)
    (hE : E' = E)
    (hK : K' = K)
    (hS : S' = S)
    (hQ : Q' = Q)
    (hF : F' = F)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    WeakOmniscienceBoundaryUp.mk R' E' K' S' Q' F' H' C' P' N' =
      WeakOmniscienceBoundaryUp.mk R E K S Q F H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hE
  cases hK
  cases hS
  cases hQ
  cases hF
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private def weakOmniscienceBoundaryToEventFlow : WeakOmniscienceBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | WeakOmniscienceBoundaryUp.mk R E K S Q F H C P N =>
      [[BMark.b0],
        weakOmniscienceBoundaryEncodeBHist R,
        [BMark.b1, BMark.b0],
        weakOmniscienceBoundaryEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b0],
        weakOmniscienceBoundaryEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        weakOmniscienceBoundaryEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        weakOmniscienceBoundaryEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        weakOmniscienceBoundaryEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        weakOmniscienceBoundaryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        weakOmniscienceBoundaryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        weakOmniscienceBoundaryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        weakOmniscienceBoundaryEncodeBHist N]

private def weakOmniscienceBoundaryFromEventFlow :
    EventFlow → Option WeakOmniscienceBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | K :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | S :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | Q :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | F :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (WeakOmniscienceBoundaryUp.mk
                                                                                          (weakOmniscienceBoundaryDecodeBHist R)
                                                                                          (weakOmniscienceBoundaryDecodeBHist E)
                                                                                          (weakOmniscienceBoundaryDecodeBHist K)
                                                                                          (weakOmniscienceBoundaryDecodeBHist S)
                                                                                          (weakOmniscienceBoundaryDecodeBHist Q)
                                                                                          (weakOmniscienceBoundaryDecodeBHist F)
                                                                                          (weakOmniscienceBoundaryDecodeBHist H)
                                                                                          (weakOmniscienceBoundaryDecodeBHist C)
                                                                                          (weakOmniscienceBoundaryDecodeBHist P)
                                                                                          (weakOmniscienceBoundaryDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem weakOmniscienceBoundary_round_trip :
    ∀ x : WeakOmniscienceBoundaryUp,
      weakOmniscienceBoundaryFromEventFlow
        (weakOmniscienceBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R E K S Q F H C P N =>
      change
        some
          (WeakOmniscienceBoundaryUp.mk
            (weakOmniscienceBoundaryDecodeBHist (weakOmniscienceBoundaryEncodeBHist R))
            (weakOmniscienceBoundaryDecodeBHist (weakOmniscienceBoundaryEncodeBHist E))
            (weakOmniscienceBoundaryDecodeBHist (weakOmniscienceBoundaryEncodeBHist K))
            (weakOmniscienceBoundaryDecodeBHist (weakOmniscienceBoundaryEncodeBHist S))
            (weakOmniscienceBoundaryDecodeBHist (weakOmniscienceBoundaryEncodeBHist Q))
            (weakOmniscienceBoundaryDecodeBHist (weakOmniscienceBoundaryEncodeBHist F))
            (weakOmniscienceBoundaryDecodeBHist (weakOmniscienceBoundaryEncodeBHist H))
            (weakOmniscienceBoundaryDecodeBHist (weakOmniscienceBoundaryEncodeBHist C))
            (weakOmniscienceBoundaryDecodeBHist (weakOmniscienceBoundaryEncodeBHist P))
            (weakOmniscienceBoundaryDecodeBHist (weakOmniscienceBoundaryEncodeBHist N))) =
          some (WeakOmniscienceBoundaryUp.mk R E K S Q F H C P N)
      exact
        congrArg some
          (weakOmniscienceBoundary_mk_congr
            (weakOmniscienceBoundaryDecode_encode_bhist R)
            (weakOmniscienceBoundaryDecode_encode_bhist E)
            (weakOmniscienceBoundaryDecode_encode_bhist K)
            (weakOmniscienceBoundaryDecode_encode_bhist S)
            (weakOmniscienceBoundaryDecode_encode_bhist Q)
            (weakOmniscienceBoundaryDecode_encode_bhist F)
            (weakOmniscienceBoundaryDecode_encode_bhist H)
            (weakOmniscienceBoundaryDecode_encode_bhist C)
            (weakOmniscienceBoundaryDecode_encode_bhist P)
            (weakOmniscienceBoundaryDecode_encode_bhist N))

private theorem weakOmniscienceBoundaryToEventFlow_injective
    {x y : WeakOmniscienceBoundaryUp} :
    weakOmniscienceBoundaryToEventFlow x = weakOmniscienceBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weakOmniscienceBoundaryFromEventFlow (weakOmniscienceBoundaryToEventFlow x) =
        weakOmniscienceBoundaryFromEventFlow (weakOmniscienceBoundaryToEventFlow y) :=
    congrArg weakOmniscienceBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (weakOmniscienceBoundary_round_trip x).symm
      (Eq.trans hread (weakOmniscienceBoundary_round_trip y)))

instance weakOmniscienceBoundaryBHistCarrier : BHistCarrier WeakOmniscienceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weakOmniscienceBoundaryToEventFlow
  fromEventFlow := weakOmniscienceBoundaryFromEventFlow

instance weakOmniscienceBoundaryChapterTasteGate :
    ChapterTasteGate WeakOmniscienceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change weakOmniscienceBoundaryFromEventFlow
      (weakOmniscienceBoundaryToEventFlow x) = some x
    exact weakOmniscienceBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (weakOmniscienceBoundaryToEventFlow_injective heq)

theorem WeakOmniscienceBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, weakOmniscienceBoundaryDecodeBHist
      (weakOmniscienceBoundaryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier WeakOmniscienceBoundaryUp) ∧
        Nonempty (ChapterTasteGate WeakOmniscienceBoundaryUp) ∧
          weakOmniscienceBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact weakOmniscienceBoundaryDecode_encode_bhist
  · constructor
    · exact Nonempty.intro weakOmniscienceBoundaryBHistCarrier
    · constructor
      · exact Nonempty.intro weakOmniscienceBoundaryChapterTasteGate
      · rfl

end BEDC.Derived.WeakOmniscienceBoundaryUp
