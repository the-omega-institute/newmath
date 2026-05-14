import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverLocalityTransportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverLocalityTransportUp : Type where
  | mk : (O D R L H Q C P N : BHist) → ObserverLocalityTransportUp
  deriving DecidableEq

def observerLocalityTransportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerLocalityTransportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerLocalityTransportEncodeBHist h

def observerLocalityTransportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerLocalityTransportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerLocalityTransportDecodeBHist tail)

private theorem observerLocalityTransportDecode_encode_bhist :
    ∀ h : BHist,
      observerLocalityTransportDecodeBHist
        (observerLocalityTransportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerLocalityTransportToEventFlow :
    ObserverLocalityTransportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverLocalityTransportUp.mk O D R L H Q C P N =>
      [[BMark.b0],
        observerLocalityTransportEncodeBHist O,
        [BMark.b1, BMark.b0],
        observerLocalityTransportEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        observerLocalityTransportEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityTransportEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityTransportEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityTransportEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityTransportEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerLocalityTransportEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerLocalityTransportEncodeBHist N]

def observerLocalityTransportFromEventFlow :
    EventFlow → Option ObserverLocalityTransportUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | O :: rest1 =>
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
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | L :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | Q :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ObserverLocalityTransportUp.mk
                                                                                  (observerLocalityTransportDecodeBHist O)
                                                                                  (observerLocalityTransportDecodeBHist D)
                                                                                  (observerLocalityTransportDecodeBHist R)
                                                                                  (observerLocalityTransportDecodeBHist L)
                                                                                  (observerLocalityTransportDecodeBHist H)
                                                                                  (observerLocalityTransportDecodeBHist Q)
                                                                                  (observerLocalityTransportDecodeBHist C)
                                                                                  (observerLocalityTransportDecodeBHist P)
                                                                                  (observerLocalityTransportDecodeBHist N))
                                                                          | _ :: _ => none

private theorem observerLocalityTransport_round_trip :
    ∀ x : ObserverLocalityTransportUp,
      observerLocalityTransportFromEventFlow
        (observerLocalityTransportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O D R L H Q C P N =>
      change
        some
          (ObserverLocalityTransportUp.mk
            (observerLocalityTransportDecodeBHist
              (observerLocalityTransportEncodeBHist O))
            (observerLocalityTransportDecodeBHist
              (observerLocalityTransportEncodeBHist D))
            (observerLocalityTransportDecodeBHist
              (observerLocalityTransportEncodeBHist R))
            (observerLocalityTransportDecodeBHist
              (observerLocalityTransportEncodeBHist L))
            (observerLocalityTransportDecodeBHist
              (observerLocalityTransportEncodeBHist H))
            (observerLocalityTransportDecodeBHist
              (observerLocalityTransportEncodeBHist Q))
            (observerLocalityTransportDecodeBHist
              (observerLocalityTransportEncodeBHist C))
            (observerLocalityTransportDecodeBHist
              (observerLocalityTransportEncodeBHist P))
            (observerLocalityTransportDecodeBHist
              (observerLocalityTransportEncodeBHist N))) =
          some (ObserverLocalityTransportUp.mk O D R L H Q C P N)
      rw [observerLocalityTransportDecode_encode_bhist O,
        observerLocalityTransportDecode_encode_bhist D,
        observerLocalityTransportDecode_encode_bhist R,
        observerLocalityTransportDecode_encode_bhist L,
        observerLocalityTransportDecode_encode_bhist H,
        observerLocalityTransportDecode_encode_bhist Q,
        observerLocalityTransportDecode_encode_bhist C,
        observerLocalityTransportDecode_encode_bhist P,
        observerLocalityTransportDecode_encode_bhist N]

private theorem observerLocalityTransportToEventFlow_injective
    {x y : ObserverLocalityTransportUp} :
    observerLocalityTransportToEventFlow x =
      observerLocalityTransportToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerLocalityTransportFromEventFlow
          (observerLocalityTransportToEventFlow x) =
        observerLocalityTransportFromEventFlow
          (observerLocalityTransportToEventFlow y) :=
    congrArg observerLocalityTransportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerLocalityTransport_round_trip x).symm
      (Eq.trans hread (observerLocalityTransport_round_trip y)))

instance observerLocalityTransportBHistCarrier :
    BHistCarrier ObserverLocalityTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerLocalityTransportToEventFlow
  fromEventFlow := observerLocalityTransportFromEventFlow

instance observerLocalityTransportChapterTasteGate :
    ChapterTasteGate ObserverLocalityTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerLocalityTransportFromEventFlow
        (observerLocalityTransportToEventFlow x) = some x
    exact observerLocalityTransport_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerLocalityTransportToEventFlow_injective heq)

instance observerLocalityTransportFieldFaithful :
    FieldFaithful ObserverLocalityTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObserverLocalityTransportUp.mk O D R L H Q C P N => [O, D, R, L, H, Q, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk O₁ D₁ R₁ L₁ H₁ Q₁ C₁ P₁ N₁ =>
        cases y with
        | mk O₂ D₂ R₂ L₂ H₂ Q₂ C₂ P₂ N₂ =>
            injection h with hO t1
            injection t1 with hD t2
            injection t2 with hR t3
            injection t3 with hL t4
            injection t4 with hH t5
            injection t5 with hQ t6
            injection t6 with hC t7
            injection t7 with hP t8
            injection t8 with hN _
            cases hO
            cases hD
            cases hR
            cases hL
            cases hH
            cases hQ
            cases hC
            cases hP
            cases hN
            rfl

instance observerLocalityTransportNontrivial :
    Nontrivial ObserverLocalityTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverLocalityTransportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverLocalityTransportUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverLocalityTransportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem ObserverLocalityTransportTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerLocalityTransportDecodeBHist (observerLocalityTransportEncodeBHist h) = h) ∧
      (∀ x : ObserverLocalityTransportUp,
        observerLocalityTransportFromEventFlow (observerLocalityTransportToEventFlow x) =
          some x) ∧
        (∀ x y : ObserverLocalityTransportUp,
          observerLocalityTransportToEventFlow x =
            observerLocalityTransportToEventFlow y → x = y) ∧
          observerLocalityTransportEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerLocalityTransportDecode_encode_bhist
  · constructor
    · exact observerLocalityTransport_round_trip
    · constructor
      · intro x y heq
        exact observerLocalityTransportToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObserverLocalityTransportUp
