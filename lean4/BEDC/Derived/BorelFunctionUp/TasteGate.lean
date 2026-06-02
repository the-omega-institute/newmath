import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BorelFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BorelFunctionUp : Type where
  | mk (X B R Q H C P N : BHist) : BorelFunctionUp
  deriving DecidableEq

def borelFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: borelFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: borelFunctionEncodeBHist h

def borelFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (borelFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (borelFunctionDecodeBHist tail)

private theorem BorelFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, borelFunctionDecodeBHist (borelFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def borelFunctionFields : BorelFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BorelFunctionUp.mk X B R Q H C P N => [X, B, R, Q, H, C, P, N]

def borelFunctionToEventFlow : BorelFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (borelFunctionFields x).map borelFunctionEncodeBHist

def borelFunctionFromEventFlow : EventFlow → Option BorelFunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | B :: restB =>
          match restB with
          | R :: restR =>
              match restR with
              | Q :: restQ =>
                  match restQ with
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
                                        (BorelFunctionUp.mk
                                          (borelFunctionDecodeBHist X)
                                          (borelFunctionDecodeBHist B)
                                          (borelFunctionDecodeBHist R)
                                          (borelFunctionDecodeBHist Q)
                                          (borelFunctionDecodeBHist H)
                                          (borelFunctionDecodeBHist C)
                                          (borelFunctionDecodeBHist P)
                                          (borelFunctionDecodeBHist N))
                                  | _ :: _ => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem borelFunction_mk_congr
    {X X' B B' R R' Q Q' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hB : B' = B) (hR : R' = R) (hQ : Q' = Q)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    BorelFunctionUp.mk X' B' R' Q' H' C' P' N' =
      BorelFunctionUp.mk X B R Q H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hB
  cases hR
  cases hQ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem BorelFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BorelFunctionUp,
      borelFunctionFromEventFlow (borelFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X B R Q H C P N =>
      exact
        congrArg some
          (borelFunction_mk_congr
            (BorelFunctionTasteGate_single_carrier_alignment_decode X)
            (BorelFunctionTasteGate_single_carrier_alignment_decode B)
            (BorelFunctionTasteGate_single_carrier_alignment_decode R)
            (BorelFunctionTasteGate_single_carrier_alignment_decode Q)
            (BorelFunctionTasteGate_single_carrier_alignment_decode H)
            (BorelFunctionTasteGate_single_carrier_alignment_decode C)
            (BorelFunctionTasteGate_single_carrier_alignment_decode P)
            (BorelFunctionTasteGate_single_carrier_alignment_decode N))

private theorem borelFunctionToEventFlow_injective {x y : BorelFunctionUp} :
    borelFunctionToEventFlow x = borelFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      borelFunctionFromEventFlow (borelFunctionToEventFlow x) =
        borelFunctionFromEventFlow (borelFunctionToEventFlow y) :=
    congrArg borelFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BorelFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BorelFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance borelFunctionBHistCarrier : BHistCarrier BorelFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := borelFunctionToEventFlow
  fromEventFlow := borelFunctionFromEventFlow

instance borelFunctionChapterTasteGate : ChapterTasteGate BorelFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change borelFunctionFromEventFlow (borelFunctionToEventFlow x) = some x
    exact BorelFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (borelFunctionToEventFlow_injective heq)

theorem BorelFunctionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BorelFunctionUp) ∧ Nonempty (ChapterTasteGate BorelFunctionUp) ∧
      (∀ h : BHist, borelFunctionDecodeBHist (borelFunctionEncodeBHist h) = h) ∧
        (∀ x : BorelFunctionUp,
          borelFunctionFromEventFlow (borelFunctionToEventFlow x) = some x) ∧
          borelFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨borelFunctionBHistCarrier⟩
  · constructor
    · exact ⟨borelFunctionChapterTasteGate⟩
    · constructor
      · exact BorelFunctionTasteGate_single_carrier_alignment_decode
      · constructor
        · exact BorelFunctionTasteGate_single_carrier_alignment_round_trip
        · rfl

end BEDC.Derived.BorelFunctionUp
