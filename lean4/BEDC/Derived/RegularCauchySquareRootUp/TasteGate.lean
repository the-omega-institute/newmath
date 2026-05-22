import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySquareRootUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySquareRootUp : Type where
  | mk (R N W D B T M S E H C P A : BHist) : RegularCauchySquareRootUp
  deriving DecidableEq

def regularCauchySquareRootEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySquareRootEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySquareRootEncodeBHist h

def regularCauchySquareRootDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySquareRootDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySquareRootDecodeBHist tail)

private theorem regularCauchySquareRoot_decode_encode :
    ∀ h : BHist,
      regularCauchySquareRootDecodeBHist (regularCauchySquareRootEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySquareRootFields : RegularCauchySquareRootUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySquareRootUp.mk R N W D B T M S E H C P A =>
      [R, N, W, D, B, T, M, S, E, H, C, P, A]

def regularCauchySquareRootToEventFlow : RegularCauchySquareRootUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchySquareRootFields x).map regularCauchySquareRootEncodeBHist

def regularCauchySquareRootFromEventFlow :
    EventFlow → Option RegularCauchySquareRootUp
  -- BEDC touchpoint anchor: BHist BMark
  | R :: restR =>
      match restR with
      | N :: restN =>
          match restN with
          | W :: restW =>
              match restW with
              | D :: restD =>
                  match restD with
                  | B :: restB =>
                      match restB with
                      | T :: restT =>
                          match restT with
                          | M :: restM =>
                              match restM with
                              | S :: restS =>
                                  match restS with
                                  | E :: restE =>
                                      match restE with
                                      | H :: restH =>
                                          match restH with
                                          | C :: restC =>
                                              match restC with
                                              | P :: restP =>
                                                  match restP with
                                                  | A :: restA =>
                                                      match restA with
                                                      | [] =>
                                                          some
                                                            (RegularCauchySquareRootUp.mk
                                                              (regularCauchySquareRootDecodeBHist R)
                                                              (regularCauchySquareRootDecodeBHist N)
                                                              (regularCauchySquareRootDecodeBHist W)
                                                              (regularCauchySquareRootDecodeBHist D)
                                                              (regularCauchySquareRootDecodeBHist B)
                                                              (regularCauchySquareRootDecodeBHist T)
                                                              (regularCauchySquareRootDecodeBHist M)
                                                              (regularCauchySquareRootDecodeBHist S)
                                                              (regularCauchySquareRootDecodeBHist E)
                                                              (regularCauchySquareRootDecodeBHist H)
                                                              (regularCauchySquareRootDecodeBHist C)
                                                              (regularCauchySquareRootDecodeBHist P)
                                                              (regularCauchySquareRootDecodeBHist A))
                                                      | _ :: _ => none
                                                  | [] => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem regularCauchySquareRoot_mk_congr
    {R R' N N' W W' D D' B B' T T' M M' S S' E E' H H' C C' P P' A A' : BHist}
    (hR : R' = R) (hN : N' = N) (hW : W' = W) (hD : D' = D)
    (hB : B' = B) (hT : T' = T) (hM : M' = M) (hS : S' = S)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hA : A' = A) :
    RegularCauchySquareRootUp.mk R' N' W' D' B' T' M' S' E' H' C' P' A' =
      RegularCauchySquareRootUp.mk R N W D B T M S E H C P A := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hN
  cases hW
  cases hD
  cases hB
  cases hT
  cases hM
  cases hS
  cases hE
  cases hH
  cases hC
  cases hP
  cases hA
  rfl

private theorem regularCauchySquareRoot_round_trip :
    ∀ x : RegularCauchySquareRootUp,
      regularCauchySquareRootFromEventFlow (regularCauchySquareRootToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R N W D B T M S E H C P A =>
      exact
        congrArg some
          (regularCauchySquareRoot_mk_congr
            (regularCauchySquareRoot_decode_encode R)
            (regularCauchySquareRoot_decode_encode N)
            (regularCauchySquareRoot_decode_encode W)
            (regularCauchySquareRoot_decode_encode D)
            (regularCauchySquareRoot_decode_encode B)
            (regularCauchySquareRoot_decode_encode T)
            (regularCauchySquareRoot_decode_encode M)
            (regularCauchySquareRoot_decode_encode S)
            (regularCauchySquareRoot_decode_encode E)
            (regularCauchySquareRoot_decode_encode H)
            (regularCauchySquareRoot_decode_encode C)
            (regularCauchySquareRoot_decode_encode P)
            (regularCauchySquareRoot_decode_encode A))

private theorem regularCauchySquareRootToEventFlow_injective
    {x y : RegularCauchySquareRootUp} :
    regularCauchySquareRootToEventFlow x = regularCauchySquareRootToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySquareRootFromEventFlow (regularCauchySquareRootToEventFlow x) =
        regularCauchySquareRootFromEventFlow (regularCauchySquareRootToEventFlow y) :=
    congrArg regularCauchySquareRootFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySquareRoot_round_trip x).symm
      (Eq.trans hread (regularCauchySquareRoot_round_trip y)))

instance regularCauchySquareRootBHistCarrier :
    BHistCarrier RegularCauchySquareRootUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySquareRootToEventFlow
  fromEventFlow := regularCauchySquareRootFromEventFlow

instance regularCauchySquareRootChapterTasteGate :
    ChapterTasteGate RegularCauchySquareRootUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySquareRootFromEventFlow (regularCauchySquareRootToEventFlow x) =
      some x
    exact regularCauchySquareRoot_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySquareRootToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySquareRootUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySquareRootChapterTasteGate

theorem RegularCauchySquareRootUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySquareRootDecodeBHist (regularCauchySquareRootEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySquareRootUp,
        regularCauchySquareRootFromEventFlow (regularCauchySquareRootToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchySquareRootUp,
        regularCauchySquareRootToEventFlow x = regularCauchySquareRootToEventFlow y →
          x = y) ∧
      regularCauchySquareRootEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchySquareRoot_decode_encode
  constructor
  · exact regularCauchySquareRoot_round_trip
  constructor
  · intro x y heq
    exact regularCauchySquareRootToEventFlow_injective heq
  · rfl

end BEDC.Derived.RegularCauchySquareRootUp.TasteGate
