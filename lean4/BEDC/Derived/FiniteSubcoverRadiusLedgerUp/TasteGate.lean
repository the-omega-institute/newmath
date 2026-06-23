import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSubcoverRadiusLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSubcoverRadiusLedgerUp : Type where
  | mk (K F G R B U H C P N : BHist) : FiniteSubcoverRadiusLedgerUp
  deriving DecidableEq

def finiteSubcoverRadiusLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSubcoverRadiusLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSubcoverRadiusLedgerEncodeBHist h

def finiteSubcoverRadiusLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSubcoverRadiusLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSubcoverRadiusLedgerDecodeBHist tail)

private theorem finiteSubcoverRadiusLedgerDecode_encode_bhist :
    ∀ h : BHist,
      finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteSubcoverRadiusLedgerToEventFlow :
    FiniteSubcoverRadiusLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSubcoverRadiusLedgerUp.mk K F G R B U H C P N =>
      [[BMark.b0],
        finiteSubcoverRadiusLedgerEncodeBHist K,
        [BMark.b1, BMark.b0],
        finiteSubcoverRadiusLedgerEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteSubcoverRadiusLedgerEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteSubcoverRadiusLedgerEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteSubcoverRadiusLedgerEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteSubcoverRadiusLedgerEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteSubcoverRadiusLedgerEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteSubcoverRadiusLedgerEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteSubcoverRadiusLedgerEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteSubcoverRadiusLedgerEncodeBHist N]

def finiteSubcoverRadiusLedgerFromEventFlow :
    EventFlow → Option FiniteSubcoverRadiusLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | K :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | G :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | B :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | U :: rest11 =>
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
                                                                                        (FiniteSubcoverRadiusLedgerUp.mk
                                                                                          (finiteSubcoverRadiusLedgerDecodeBHist
                                                                                            K)
                                                                                          (finiteSubcoverRadiusLedgerDecodeBHist
                                                                                            F)
                                                                                          (finiteSubcoverRadiusLedgerDecodeBHist
                                                                                            G)
                                                                                          (finiteSubcoverRadiusLedgerDecodeBHist
                                                                                            R)
                                                                                          (finiteSubcoverRadiusLedgerDecodeBHist
                                                                                            B)
                                                                                          (finiteSubcoverRadiusLedgerDecodeBHist
                                                                                            U)
                                                                                          (finiteSubcoverRadiusLedgerDecodeBHist
                                                                                            H)
                                                                                          (finiteSubcoverRadiusLedgerDecodeBHist
                                                                                            C)
                                                                                          (finiteSubcoverRadiusLedgerDecodeBHist
                                                                                            P)
                                                                                          (finiteSubcoverRadiusLedgerDecodeBHist
                                                                                            N))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem finiteSubcoverRadiusLedger_round_trip :
    ∀ x : FiniteSubcoverRadiusLedgerUp,
      finiteSubcoverRadiusLedgerFromEventFlow
        (finiteSubcoverRadiusLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F G R B U H C P N =>
      change
        some
          (FiniteSubcoverRadiusLedgerUp.mk
            (finiteSubcoverRadiusLedgerDecodeBHist
              (finiteSubcoverRadiusLedgerEncodeBHist K))
            (finiteSubcoverRadiusLedgerDecodeBHist
              (finiteSubcoverRadiusLedgerEncodeBHist F))
            (finiteSubcoverRadiusLedgerDecodeBHist
              (finiteSubcoverRadiusLedgerEncodeBHist G))
            (finiteSubcoverRadiusLedgerDecodeBHist
              (finiteSubcoverRadiusLedgerEncodeBHist R))
            (finiteSubcoverRadiusLedgerDecodeBHist
              (finiteSubcoverRadiusLedgerEncodeBHist B))
            (finiteSubcoverRadiusLedgerDecodeBHist
              (finiteSubcoverRadiusLedgerEncodeBHist U))
            (finiteSubcoverRadiusLedgerDecodeBHist
              (finiteSubcoverRadiusLedgerEncodeBHist H))
            (finiteSubcoverRadiusLedgerDecodeBHist
              (finiteSubcoverRadiusLedgerEncodeBHist C))
            (finiteSubcoverRadiusLedgerDecodeBHist
              (finiteSubcoverRadiusLedgerEncodeBHist P))
            (finiteSubcoverRadiusLedgerDecodeBHist
              (finiteSubcoverRadiusLedgerEncodeBHist N))) =
          some (FiniteSubcoverRadiusLedgerUp.mk K F G R B U H C P N)
      rw [finiteSubcoverRadiusLedgerDecode_encode_bhist K,
        finiteSubcoverRadiusLedgerDecode_encode_bhist F,
        finiteSubcoverRadiusLedgerDecode_encode_bhist G,
        finiteSubcoverRadiusLedgerDecode_encode_bhist R,
        finiteSubcoverRadiusLedgerDecode_encode_bhist B,
        finiteSubcoverRadiusLedgerDecode_encode_bhist U,
        finiteSubcoverRadiusLedgerDecode_encode_bhist H,
        finiteSubcoverRadiusLedgerDecode_encode_bhist C,
        finiteSubcoverRadiusLedgerDecode_encode_bhist P,
        finiteSubcoverRadiusLedgerDecode_encode_bhist N]

private theorem finiteSubcoverRadiusLedgerToEventFlow_injective
    {x y : FiniteSubcoverRadiusLedgerUp} :
    finiteSubcoverRadiusLedgerToEventFlow x =
      finiteSubcoverRadiusLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSubcoverRadiusLedgerFromEventFlow
          (finiteSubcoverRadiusLedgerToEventFlow x) =
        finiteSubcoverRadiusLedgerFromEventFlow
          (finiteSubcoverRadiusLedgerToEventFlow y) :=
    congrArg finiteSubcoverRadiusLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteSubcoverRadiusLedger_round_trip x).symm
      (Eq.trans hread (finiteSubcoverRadiusLedger_round_trip y)))

instance finiteSubcoverRadiusLedgerBHistCarrier :
    BHistCarrier FiniteSubcoverRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSubcoverRadiusLedgerToEventFlow
  fromEventFlow := finiteSubcoverRadiusLedgerFromEventFlow

instance finiteSubcoverRadiusLedgerChapterTasteGate :
    ChapterTasteGate FiniteSubcoverRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteSubcoverRadiusLedgerFromEventFlow
        (finiteSubcoverRadiusLedgerToEventFlow x) = some x
    exact finiteSubcoverRadiusLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteSubcoverRadiusLedgerToEventFlow_injective heq)

theorem FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteSubcoverRadiusLedgerUp) ∧
      Nonempty (ChapterTasteGate FiniteSubcoverRadiusLedgerUp) ∧
      finiteSubcoverRadiusLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteSubcoverRadiusLedgerDecode_encode_bhist
  · constructor
    · exact ⟨finiteSubcoverRadiusLedgerBHistCarrier⟩
    · constructor
      · exact ⟨finiteSubcoverRadiusLedgerChapterTasteGate⟩
      · rfl

end BEDC.Derived.FiniteSubcoverRadiusLedgerUp
