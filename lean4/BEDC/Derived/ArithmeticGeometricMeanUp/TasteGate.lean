import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArithmeticGeometricMeanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArithmeticGeometricMeanUp : Type where
  | mk (X Y A G D S Q E H C P N : BHist) : ArithmeticGeometricMeanUp
  deriving DecidableEq

def arithmeticGeometricMeanEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: arithmeticGeometricMeanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: arithmeticGeometricMeanEncodeBHist h

def arithmeticGeometricMeanDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (arithmeticGeometricMeanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (arithmeticGeometricMeanDecodeBHist tail)

private theorem ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      arithmeticGeometricMeanDecodeBHist (arithmeticGeometricMeanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def arithmeticGeometricMeanFields : ArithmeticGeometricMeanUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArithmeticGeometricMeanUp.mk X Y A G D S Q E H C P N => [X, Y, A, G, D, S, Q, E, H, C, P, N]

def arithmeticGeometricMeanToEventFlow : ArithmeticGeometricMeanUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (arithmeticGeometricMeanFields x).map arithmeticGeometricMeanEncodeBHist

def arithmeticGeometricMeanFromEventFlow : EventFlow → Option ArithmeticGeometricMeanUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | Y :: restY =>
          match restY with
          | A :: restA =>
              match restA with
              | G :: restG =>
                  match restG with
                  | D :: restD =>
                      match restD with
                      | S :: restS =>
                          match restS with
                          | Q :: restQ =>
                              match restQ with
                              | E :: restE =>
                                  match restE with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (ArithmeticGeometricMeanUp.mk
                                                          (arithmeticGeometricMeanDecodeBHist X)
                                                          (arithmeticGeometricMeanDecodeBHist Y)
                                                          (arithmeticGeometricMeanDecodeBHist A)
                                                          (arithmeticGeometricMeanDecodeBHist G)
                                                          (arithmeticGeometricMeanDecodeBHist D)
                                                          (arithmeticGeometricMeanDecodeBHist S)
                                                          (arithmeticGeometricMeanDecodeBHist Q)
                                                          (arithmeticGeometricMeanDecodeBHist E)
                                                          (arithmeticGeometricMeanDecodeBHist H)
                                                          (arithmeticGeometricMeanDecodeBHist C)
                                                          (arithmeticGeometricMeanDecodeBHist P)
                                                          (arithmeticGeometricMeanDecodeBHist N))
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

private theorem arithmeticGeometricMean_mk_congr
    {X X' Y Y' A A' G G' D D' S S' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hY : Y' = Y) (hA : A' = A) (hG : G' = G)
    (hD : D' = D) (hS : S' = S) (hQ : Q' = Q) (hE : E' = E)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    ArithmeticGeometricMeanUp.mk X' Y' A' G' D' S' Q' E' H' C' P' N' =
      ArithmeticGeometricMeanUp.mk X Y A G D S Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hA
  cases hG
  cases hD
  cases hS
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem ArithmeticGeometricMeanTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ArithmeticGeometricMeanUp,
      arithmeticGeometricMeanFromEventFlow
        (arithmeticGeometricMeanToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y A G D S Q E H C P N =>
      exact
        congrArg some
          (arithmeticGeometricMean_mk_congr
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode X)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode Y)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode A)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode G)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode D)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode S)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode Q)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode E)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode H)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode C)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode P)
            (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode N))

private theorem arithmeticGeometricMeanToEventFlow_injective
    {x y : ArithmeticGeometricMeanUp} :
    arithmeticGeometricMeanToEventFlow x =
      arithmeticGeometricMeanToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      arithmeticGeometricMeanFromEventFlow (arithmeticGeometricMeanToEventFlow x) =
        arithmeticGeometricMeanFromEventFlow (arithmeticGeometricMeanToEventFlow y) :=
    congrArg arithmeticGeometricMeanFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArithmeticGeometricMeanTasteGate_single_carrier_alignment_round_trip y)))

instance arithmeticGeometricMeanBHistCarrier :
    BHistCarrier ArithmeticGeometricMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := arithmeticGeometricMeanToEventFlow
  fromEventFlow := arithmeticGeometricMeanFromEventFlow

instance arithmeticGeometricMeanChapterTasteGate :
    ChapterTasteGate ArithmeticGeometricMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      arithmeticGeometricMeanFromEventFlow
        (arithmeticGeometricMeanToEventFlow x) = some x
    exact ArithmeticGeometricMeanTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (arithmeticGeometricMeanToEventFlow_injective heq)

theorem ArithmeticGeometricMeanTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      arithmeticGeometricMeanDecodeBHist (arithmeticGeometricMeanEncodeBHist h) = h) ∧
      (∀ x : ArithmeticGeometricMeanUp,
        arithmeticGeometricMeanFromEventFlow
          (arithmeticGeometricMeanToEventFlow x) = some x) ∧
        (∀ x y : ArithmeticGeometricMeanUp,
          arithmeticGeometricMeanToEventFlow x = arithmeticGeometricMeanToEventFlow y →
            x = y) ∧
          arithmeticGeometricMeanEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ArithmeticGeometricMeanTasteGate_single_carrier_alignment_decode
  constructor
  · exact ArithmeticGeometricMeanTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact arithmeticGeometricMeanToEventFlow_injective heq
  · rfl

end BEDC.Derived.ArithmeticGeometricMeanUp
