import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhilosophyCannotClaimRegistryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhilosophyCannotClaimRegistryUp : Type where
  | mk (C S E U B H K P N : BHist) : PhilosophyCannotClaimRegistryUp
  deriving DecidableEq

def philosophyCannotClaimRegistryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: philosophyCannotClaimRegistryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: philosophyCannotClaimRegistryEncodeBHist h

def philosophyCannotClaimRegistryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (philosophyCannotClaimRegistryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (philosophyCannotClaimRegistryDecodeBHist tail)

private theorem philosophyCannotClaimRegistryDecode_encode_bhist :
    ∀ h : BHist,
      philosophyCannotClaimRegistryDecodeBHist
        (philosophyCannotClaimRegistryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem philosophyCannotClaimRegistry_mk_congr
    {C C' S S' E E' U U' B B' H H' K K' P P' N N' : BHist}
    (hC : C' = C) (hS : S' = S) (hE : E' = E) (hU : U' = U)
    (hB : B' = B) (hH : H' = H) (hK : K' = K) (hP : P' = P)
    (hN : N' = N) :
    PhilosophyCannotClaimRegistryUp.mk C' S' E' U' B' H' K' P' N' =
      PhilosophyCannotClaimRegistryUp.mk C S E U B H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hC
  cases hS
  cases hE
  cases hU
  cases hB
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

def philosophyCannotClaimRegistryToEventFlow :
    PhilosophyCannotClaimRegistryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyCannotClaimRegistryUp.mk C S E U B H K P N =>
      [[BMark.b0],
        philosophyCannotClaimRegistryEncodeBHist C,
        [BMark.b1, BMark.b0],
        philosophyCannotClaimRegistryEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        philosophyCannotClaimRegistryEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyCannotClaimRegistryEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyCannotClaimRegistryEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyCannotClaimRegistryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyCannotClaimRegistryEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        philosophyCannotClaimRegistryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        philosophyCannotClaimRegistryEncodeBHist N]

def philosophyCannotClaimRegistryFromEventFlow :
    EventFlow → Option PhilosophyCannotClaimRegistryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | C :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | U :: rest7 =>
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
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | K :: rest13 =>
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
                                                                                (PhilosophyCannotClaimRegistryUp.mk
                                                                                  (philosophyCannotClaimRegistryDecodeBHist C)
                                                                                  (philosophyCannotClaimRegistryDecodeBHist S)
                                                                                  (philosophyCannotClaimRegistryDecodeBHist E)
                                                                                  (philosophyCannotClaimRegistryDecodeBHist U)
                                                                                  (philosophyCannotClaimRegistryDecodeBHist B)
                                                                                  (philosophyCannotClaimRegistryDecodeBHist H)
                                                                                  (philosophyCannotClaimRegistryDecodeBHist K)
                                                                                  (philosophyCannotClaimRegistryDecodeBHist P)
                                                                                  (philosophyCannotClaimRegistryDecodeBHist N))
                                                                          | _ :: _ => none

private theorem philosophyCannotClaimRegistry_round_trip :
    ∀ x : PhilosophyCannotClaimRegistryUp,
      philosophyCannotClaimRegistryFromEventFlow
        (philosophyCannotClaimRegistryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C S E U B H K P N =>
      change
        some
          (PhilosophyCannotClaimRegistryUp.mk
            (philosophyCannotClaimRegistryDecodeBHist
              (philosophyCannotClaimRegistryEncodeBHist C))
            (philosophyCannotClaimRegistryDecodeBHist
              (philosophyCannotClaimRegistryEncodeBHist S))
            (philosophyCannotClaimRegistryDecodeBHist
              (philosophyCannotClaimRegistryEncodeBHist E))
            (philosophyCannotClaimRegistryDecodeBHist
              (philosophyCannotClaimRegistryEncodeBHist U))
            (philosophyCannotClaimRegistryDecodeBHist
              (philosophyCannotClaimRegistryEncodeBHist B))
            (philosophyCannotClaimRegistryDecodeBHist
              (philosophyCannotClaimRegistryEncodeBHist H))
            (philosophyCannotClaimRegistryDecodeBHist
              (philosophyCannotClaimRegistryEncodeBHist K))
            (philosophyCannotClaimRegistryDecodeBHist
              (philosophyCannotClaimRegistryEncodeBHist P))
            (philosophyCannotClaimRegistryDecodeBHist
              (philosophyCannotClaimRegistryEncodeBHist N))) =
          some (PhilosophyCannotClaimRegistryUp.mk C S E U B H K P N)
      exact
        congrArg some
          (philosophyCannotClaimRegistry_mk_congr
            (philosophyCannotClaimRegistryDecode_encode_bhist C)
            (philosophyCannotClaimRegistryDecode_encode_bhist S)
            (philosophyCannotClaimRegistryDecode_encode_bhist E)
            (philosophyCannotClaimRegistryDecode_encode_bhist U)
            (philosophyCannotClaimRegistryDecode_encode_bhist B)
            (philosophyCannotClaimRegistryDecode_encode_bhist H)
            (philosophyCannotClaimRegistryDecode_encode_bhist K)
            (philosophyCannotClaimRegistryDecode_encode_bhist P)
            (philosophyCannotClaimRegistryDecode_encode_bhist N))

private theorem philosophyCannotClaimRegistryToEventFlow_injective
    {x y : PhilosophyCannotClaimRegistryUp} :
    philosophyCannotClaimRegistryToEventFlow x =
      philosophyCannotClaimRegistryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      philosophyCannotClaimRegistryFromEventFlow
          (philosophyCannotClaimRegistryToEventFlow x) =
        philosophyCannotClaimRegistryFromEventFlow
          (philosophyCannotClaimRegistryToEventFlow y) :=
    congrArg philosophyCannotClaimRegistryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (philosophyCannotClaimRegistry_round_trip x).symm
      (Eq.trans hread (philosophyCannotClaimRegistry_round_trip y)))

def philosophyCannotClaimRegistryFields :
    PhilosophyCannotClaimRegistryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyCannotClaimRegistryUp.mk C S E U B H K P N =>
      [C, S, E, U, B, H, K, P, N]

private theorem philosophyCannotClaimRegistry_field_faithful :
    ∀ x y : PhilosophyCannotClaimRegistryUp,
      philosophyCannotClaimRegistryFields x =
        philosophyCannotClaimRegistryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C S E U B H K P N =>
      cases y with
      | mk C' S' E' U' B' H' K' P' N' =>
          injection hfields with hC htail0
          injection htail0 with hS htail1
          injection htail1 with hE htail2
          injection htail2 with hU htail3
          injection htail3 with hB htail4
          injection htail4 with hH htail5
          injection htail5 with hK htail6
          injection htail6 with hP htail7
          injection htail7 with hN _hNil
          cases hC
          cases hS
          cases hE
          cases hU
          cases hB
          cases hH
          cases hK
          cases hP
          cases hN
          rfl

instance philosophyCannotClaimRegistryBHistCarrier :
    BHistCarrier PhilosophyCannotClaimRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := philosophyCannotClaimRegistryToEventFlow
  fromEventFlow := philosophyCannotClaimRegistryFromEventFlow

instance philosophyCannotClaimRegistryChapterTasteGate :
    ChapterTasteGate PhilosophyCannotClaimRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      philosophyCannotClaimRegistryFromEventFlow
        (philosophyCannotClaimRegistryToEventFlow x) = some x
    exact philosophyCannotClaimRegistry_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (philosophyCannotClaimRegistryToEventFlow_injective heq)

instance philosophyCannotClaimRegistryFieldFaithful :
    FieldFaithful PhilosophyCannotClaimRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := philosophyCannotClaimRegistryFields
  field_faithful := philosophyCannotClaimRegistry_field_faithful

instance philosophyCannotClaimRegistryNontrivial :
    Nontrivial PhilosophyCannotClaimRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhilosophyCannotClaimRegistryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhilosophyCannotClaimRegistryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhilosophyCannotClaimRegistryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  philosophyCannotClaimRegistryChapterTasteGate

theorem PhilosophyCannotClaimRegistryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      philosophyCannotClaimRegistryDecodeBHist
        (philosophyCannotClaimRegistryEncodeBHist h) = h) ∧
      (∀ x : PhilosophyCannotClaimRegistryUp,
        philosophyCannotClaimRegistryFromEventFlow
          (philosophyCannotClaimRegistryToEventFlow x) = some x) ∧
        (∀ x y : PhilosophyCannotClaimRegistryUp,
          philosophyCannotClaimRegistryToEventFlow x =
            philosophyCannotClaimRegistryToEventFlow y → x = y) ∧
          philosophyCannotClaimRegistryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨philosophyCannotClaimRegistryDecode_encode_bhist,
      philosophyCannotClaimRegistry_round_trip,
      (fun _ _ heq => philosophyCannotClaimRegistryToEventFlow_injective heq), rfl⟩

end BEDC.Derived.PhilosophyCannotClaimRegistryUp
