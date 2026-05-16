import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionFrontierUp : Type where
  | mk (D S R L M A T E H C P N : BHist) : RegularCauchyCompletionFrontierUp
  deriving DecidableEq

def regularCauchyCompletionFrontierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionFrontierEncodeBHist h

def regularCauchyCompletionFrontierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionFrontierDecodeBHist tail)

private theorem regularCauchyCompletionFrontier_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyCompletionFrontierDecodeBHist
        (regularCauchyCompletionFrontierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionFrontierToEventFlow :
    RegularCauchyCompletionFrontierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionFrontierUp.mk D S R L M A T E H C P N =>
      [regularCauchyCompletionFrontierEncodeBHist D,
        regularCauchyCompletionFrontierEncodeBHist S,
        regularCauchyCompletionFrontierEncodeBHist R,
        regularCauchyCompletionFrontierEncodeBHist L,
        regularCauchyCompletionFrontierEncodeBHist M,
        regularCauchyCompletionFrontierEncodeBHist A,
        regularCauchyCompletionFrontierEncodeBHist T,
        regularCauchyCompletionFrontierEncodeBHist E,
        regularCauchyCompletionFrontierEncodeBHist H,
        regularCauchyCompletionFrontierEncodeBHist C,
        regularCauchyCompletionFrontierEncodeBHist P,
        regularCauchyCompletionFrontierEncodeBHist N]

def regularCauchyCompletionFrontierFromEventFlow :
    EventFlow → Option RegularCauchyCompletionFrontierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: restD =>
      match restD with
      | [] => none
      | S :: restS =>
          match restS with
          | [] => none
          | R :: restR =>
              match restR with
              | [] => none
              | L :: restL =>
                  match restL with
                  | [] => none
                  | M :: restM =>
                      match restM with
                      | [] => none
                      | A :: restA =>
                          match restA with
                          | [] => none
                          | T :: restT =>
                              match restT with
                              | [] => none
                              | E :: restE =>
                                  match restE with
                                  | [] => none
                                  | H :: restH =>
                                      match restH with
                                      | [] => none
                                      | C :: restC =>
                                          match restC with
                                          | [] => none
                                          | P :: restP =>
                                              match restP with
                                              | [] => none
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (RegularCauchyCompletionFrontierUp.mk
                                                          (regularCauchyCompletionFrontierDecodeBHist D)
                                                          (regularCauchyCompletionFrontierDecodeBHist S)
                                                          (regularCauchyCompletionFrontierDecodeBHist R)
                                                          (regularCauchyCompletionFrontierDecodeBHist L)
                                                          (regularCauchyCompletionFrontierDecodeBHist M)
                                                          (regularCauchyCompletionFrontierDecodeBHist A)
                                                          (regularCauchyCompletionFrontierDecodeBHist T)
                                                          (regularCauchyCompletionFrontierDecodeBHist E)
                                                          (regularCauchyCompletionFrontierDecodeBHist H)
                                                          (regularCauchyCompletionFrontierDecodeBHist C)
                                                          (regularCauchyCompletionFrontierDecodeBHist P)
                                                          (regularCauchyCompletionFrontierDecodeBHist N))
                                                  | _ :: _ => none

private theorem regularCauchyCompletionFrontier_round_trip :
    ∀ x : RegularCauchyCompletionFrontierUp,
      regularCauchyCompletionFrontierFromEventFlow
        (regularCauchyCompletionFrontierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R L M A T E H C P N =>
      change
        some
          (RegularCauchyCompletionFrontierUp.mk
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist D))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist S))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist R))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist L))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist M))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist A))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist T))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist E))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist H))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist C))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist P))
            (regularCauchyCompletionFrontierDecodeBHist
              (regularCauchyCompletionFrontierEncodeBHist N))) =
          some (RegularCauchyCompletionFrontierUp.mk D S R L M A T E H C P N)
      congr
      · exact regularCauchyCompletionFrontier_decode_encode_bhist D
      · exact regularCauchyCompletionFrontier_decode_encode_bhist S
      · exact regularCauchyCompletionFrontier_decode_encode_bhist R
      · exact regularCauchyCompletionFrontier_decode_encode_bhist L
      · exact regularCauchyCompletionFrontier_decode_encode_bhist M
      · exact regularCauchyCompletionFrontier_decode_encode_bhist A
      · exact regularCauchyCompletionFrontier_decode_encode_bhist T
      · exact regularCauchyCompletionFrontier_decode_encode_bhist E
      · exact regularCauchyCompletionFrontier_decode_encode_bhist H
      · exact regularCauchyCompletionFrontier_decode_encode_bhist C
      · exact regularCauchyCompletionFrontier_decode_encode_bhist P
      · exact regularCauchyCompletionFrontier_decode_encode_bhist N

private theorem regularCauchyCompletionFrontierToEventFlow_injective
    {x y : RegularCauchyCompletionFrontierUp} :
    regularCauchyCompletionFrontierToEventFlow x =
      regularCauchyCompletionFrontierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionFrontierFromEventFlow
          (regularCauchyCompletionFrontierToEventFlow x) =
        regularCauchyCompletionFrontierFromEventFlow
          (regularCauchyCompletionFrontierToEventFlow y) :=
    congrArg regularCauchyCompletionFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCompletionFrontier_round_trip x).symm
      (Eq.trans hread (regularCauchyCompletionFrontier_round_trip y)))

instance regularCauchyCompletionFrontierBHistCarrier :
    BHistCarrier RegularCauchyCompletionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionFrontierToEventFlow
  fromEventFlow := regularCauchyCompletionFrontierFromEventFlow

instance regularCauchyCompletionFrontierChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionFrontierFromEventFlow
        (regularCauchyCompletionFrontierToEventFlow x) = some x
    exact regularCauchyCompletionFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCompletionFrontierToEventFlow_injective heq)

instance regularCauchyCompletionFrontierFieldFaithful :
    FieldFaithful RegularCauchyCompletionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RegularCauchyCompletionFrontierUp.mk D S R L M A T E H C P N =>
        [D, S, R, L, M, A, T, E, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk D1 S1 R1 L1 M1 A1 T1 E1 H1 C1 P1 N1 =>
        cases y with
        | mk D2 S2 R2 L2 M2 A2 T2 E2 H2 C2 P2 N2 =>
            cases h
            rfl

instance regularCauchyCompletionFrontierNontrivial :
    Nontrivial RegularCauchyCompletionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCompletionFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyCompletionFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyCompletionFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem RegularCauchyCompletionFrontierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCompletionFrontierDecodeBHist
        (regularCauchyCompletionFrontierEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyCompletionFrontierUp,
        regularCauchyCompletionFrontierFromEventFlow
          (regularCauchyCompletionFrontierToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyCompletionFrontierUp,
          regularCauchyCompletionFrontierToEventFlow x =
            regularCauchyCompletionFrontierToEventFlow y → x = y) ∧
          regularCauchyCompletionFrontierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyCompletionFrontier_decode_encode_bhist
  · constructor
    · exact regularCauchyCompletionFrontier_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyCompletionFrontierToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyCompletionFrontierUp
