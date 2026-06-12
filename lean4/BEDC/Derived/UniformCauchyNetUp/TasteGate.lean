import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchyNetUp : Type where
  | mk (D E W R S H C P N : BHist) : UniformCauchyNetUp

def uniformCauchyNetEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchyNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchyNetEncodeBHist h

def uniformCauchyNetDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchyNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchyNetDecodeBHist tail)

private theorem uniformCauchyNetDecodeEncode :
    forall h : BHist, uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCauchyNetFields : UniformCauchyNetUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyNetUp.mk D E W R S H C P N => [D, E, W, R, S, H, C, P, N]

def uniformCauchyNetToEventFlow : UniformCauchyNetUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyNetUp.mk D E W R S H C P N =>
      [uniformCauchyNetEncodeBHist D,
        uniformCauchyNetEncodeBHist E,
        uniformCauchyNetEncodeBHist W,
        uniformCauchyNetEncodeBHist R,
        uniformCauchyNetEncodeBHist S,
        uniformCauchyNetEncodeBHist H,
        uniformCauchyNetEncodeBHist C,
        uniformCauchyNetEncodeBHist P,
        uniformCauchyNetEncodeBHist N]

def uniformCauchyNetFromEventFlow : EventFlow -> Option UniformCauchyNetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: restD =>
      match restD with
      | [] => none
      | E :: restE =>
          match restE with
          | [] => none
          | W :: restW =>
              match restW with
              | [] => none
              | R :: restR =>
                  match restR with
                  | [] => none
                  | S :: restS =>
                      match restS with
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
                                            (UniformCauchyNetUp.mk
                                              (uniformCauchyNetDecodeBHist D)
                                              (uniformCauchyNetDecodeBHist E)
                                              (uniformCauchyNetDecodeBHist W)
                                              (uniformCauchyNetDecodeBHist R)
                                              (uniformCauchyNetDecodeBHist S)
                                              (uniformCauchyNetDecodeBHist H)
                                              (uniformCauchyNetDecodeBHist C)
                                              (uniformCauchyNetDecodeBHist P)
                                              (uniformCauchyNetDecodeBHist N))
                                      | _ :: _ => none

private theorem uniformCauchyNet_mk_congr
    {D' E' W' R' S' H' C' P' N' D E W R S H C P N : BHist}
    (hD : D' = D) (hE : E' = E) (hW : W' = W) (hR : R' = R) (hS : S' = S)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    UniformCauchyNetUp.mk D' E' W' R' S' H' C' P' N' =
      UniformCauchyNetUp.mk D E W R S H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hE
  cases hW
  cases hR
  cases hS
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem uniformCauchyNet_round_trip :
    forall x : UniformCauchyNetUp,
      uniformCauchyNetFromEventFlow (uniformCauchyNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D E W R S H C P N =>
      change
        some
          (UniformCauchyNetUp.mk
            (uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist D))
            (uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist E))
            (uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist W))
            (uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist R))
            (uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist S))
            (uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist H))
            (uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist C))
            (uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist P))
            (uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist N))) =
          some (UniformCauchyNetUp.mk D E W R S H C P N)
      exact
        congrArg some
          (uniformCauchyNet_mk_congr
            (uniformCauchyNetDecodeEncode D)
            (uniformCauchyNetDecodeEncode E)
            (uniformCauchyNetDecodeEncode W)
            (uniformCauchyNetDecodeEncode R)
            (uniformCauchyNetDecodeEncode S)
            (uniformCauchyNetDecodeEncode H)
            (uniformCauchyNetDecodeEncode C)
            (uniformCauchyNetDecodeEncode P)
            (uniformCauchyNetDecodeEncode N))

private theorem uniformCauchyNetToEventFlow_injective {x y : UniformCauchyNetUp} :
    uniformCauchyNetToEventFlow x = uniformCauchyNetToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchyNetFromEventFlow (uniformCauchyNetToEventFlow x) =
        uniformCauchyNetFromEventFlow (uniformCauchyNetToEventFlow y) :=
    congrArg uniformCauchyNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformCauchyNet_round_trip x).symm
      (Eq.trans hread (uniformCauchyNet_round_trip y)))

private theorem uniformCauchyNet_field_faithful :
    forall x y : UniformCauchyNetUp, uniformCauchyNetFields x = uniformCauchyNetFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 E1 W1 R1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 E2 W2 R2 S2 H2 C2 P2 N2 =>
          change [D1, E1, W1, R1, S1, H1, C1, P1, N1] =
            [D2, E2, W2, R2, S2, H2, C2, P2, N2] at hfields
          cases hfields
          rfl

instance uniformCauchyNetBHistCarrier : BHistCarrier UniformCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchyNetToEventFlow
  fromEventFlow := uniformCauchyNetFromEventFlow

instance uniformCauchyNetChapterTasteGate : ChapterTasteGate UniformCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformCauchyNetFromEventFlow (uniformCauchyNetToEventFlow x) = some x
    exact uniformCauchyNet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCauchyNetToEventFlow_injective heq)

instance uniformCauchyNetFieldFaithful : FieldFaithful UniformCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformCauchyNetFields
  field_faithful := uniformCauchyNet_field_faithful

instance uniformCauchyNetNontrivial : Nontrivial UniformCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformCauchyNetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformCauchyNetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformCauchyNetTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformCauchyNetDecodeBHist (uniformCauchyNetEncodeBHist h) = h) ∧
      (∀ x : UniformCauchyNetUp,
        uniformCauchyNetFromEventFlow (uniformCauchyNetToEventFlow x) = some x) ∧
        (∀ x y : UniformCauchyNetUp,
          uniformCauchyNetToEventFlow x = uniformCauchyNetToEventFlow y -> x = y) ∧
          uniformCauchyNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact uniformCauchyNetDecodeEncode
  · constructor
    · exact uniformCauchyNet_round_trip
    · constructor
      · intro x y heq
        exact uniformCauchyNetToEventFlow_injective heq
      · rfl

end BEDC.Derived.UniformCauchyNetUp
