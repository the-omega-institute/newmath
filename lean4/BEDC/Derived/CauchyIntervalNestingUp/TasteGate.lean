import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyIntervalNestingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyIntervalNestingUp : Type where
  | mk (I B N S D R E H C P L : BHist) : CauchyIntervalNestingUp

def cauchyIntervalNestingEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyIntervalNestingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyIntervalNestingEncodeBHist h

def cauchyIntervalNestingDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyIntervalNestingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyIntervalNestingDecodeBHist tail)

private theorem cauchyIntervalNestingDecodeEncode :
    forall h : BHist,
      cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyIntervalNestingFields : CauchyIntervalNestingUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyIntervalNestingUp.mk I B N S D R E H C P L =>
      [I, B, N, S, D, R, E, H, C, P, L]

def cauchyIntervalNestingToEventFlow : CauchyIntervalNestingUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyIntervalNestingUp.mk I B N S D R E H C P L =>
      [cauchyIntervalNestingEncodeBHist I,
        cauchyIntervalNestingEncodeBHist B,
        cauchyIntervalNestingEncodeBHist N,
        cauchyIntervalNestingEncodeBHist S,
        cauchyIntervalNestingEncodeBHist D,
        cauchyIntervalNestingEncodeBHist R,
        cauchyIntervalNestingEncodeBHist E,
        cauchyIntervalNestingEncodeBHist H,
        cauchyIntervalNestingEncodeBHist C,
        cauchyIntervalNestingEncodeBHist P,
        cauchyIntervalNestingEncodeBHist L]

def cauchyIntervalNestingFromEventFlow : EventFlow -> Option CauchyIntervalNestingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: restI =>
      match restI with
      | [] => none
      | B :: restB =>
          match restB with
          | [] => none
          | N :: restN =>
              match restN with
              | [] => none
              | S :: restS =>
                  match restS with
                  | [] => none
                  | D :: restD =>
                      match restD with
                      | [] => none
                      | R :: restR =>
                          match restR with
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
                                          | L :: restL =>
                                              match restL with
                                              | [] =>
                                                  some
                                                    (CauchyIntervalNestingUp.mk
                                                      (cauchyIntervalNestingDecodeBHist I)
                                                      (cauchyIntervalNestingDecodeBHist B)
                                                      (cauchyIntervalNestingDecodeBHist N)
                                                      (cauchyIntervalNestingDecodeBHist S)
                                                      (cauchyIntervalNestingDecodeBHist D)
                                                      (cauchyIntervalNestingDecodeBHist R)
                                                      (cauchyIntervalNestingDecodeBHist E)
                                                      (cauchyIntervalNestingDecodeBHist H)
                                                      (cauchyIntervalNestingDecodeBHist C)
                                                      (cauchyIntervalNestingDecodeBHist P)
                                                      (cauchyIntervalNestingDecodeBHist L))
                                              | _ :: _ => none

private theorem cauchyIntervalNesting_mk_congr
    {I' B' N' S' D' R' E' H' C' P' L' I B N S D R E H C P L : BHist}
    (hI : I' = I) (hB : B' = B) (hN : N' = N) (hS : S' = S) (hD : D' = D)
    (hR : R' = R) (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hL : L' = L) :
    CauchyIntervalNestingUp.mk I' B' N' S' D' R' E' H' C' P' L' =
      CauchyIntervalNestingUp.mk I B N S D R E H C P L := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hB
  cases hN
  cases hS
  cases hD
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hL
  rfl

private theorem cauchyIntervalNesting_round_trip :
    forall x : CauchyIntervalNestingUp,
      cauchyIntervalNestingFromEventFlow (cauchyIntervalNestingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I B N S D R E H C P L =>
      change
        some
          (CauchyIntervalNestingUp.mk
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist I))
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist B))
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist N))
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist S))
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist D))
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist R))
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist E))
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist H))
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist C))
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist P))
            (cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist L))) =
          some (CauchyIntervalNestingUp.mk I B N S D R E H C P L)
      exact
        congrArg some
          (cauchyIntervalNesting_mk_congr
            (cauchyIntervalNestingDecodeEncode I)
            (cauchyIntervalNestingDecodeEncode B)
            (cauchyIntervalNestingDecodeEncode N)
            (cauchyIntervalNestingDecodeEncode S)
            (cauchyIntervalNestingDecodeEncode D)
            (cauchyIntervalNestingDecodeEncode R)
            (cauchyIntervalNestingDecodeEncode E)
            (cauchyIntervalNestingDecodeEncode H)
            (cauchyIntervalNestingDecodeEncode C)
            (cauchyIntervalNestingDecodeEncode P)
            (cauchyIntervalNestingDecodeEncode L))

private theorem cauchyIntervalNestingToEventFlow_injective {x y : CauchyIntervalNestingUp} :
    cauchyIntervalNestingToEventFlow x = cauchyIntervalNestingToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyIntervalNestingFromEventFlow (cauchyIntervalNestingToEventFlow x) =
        cauchyIntervalNestingFromEventFlow (cauchyIntervalNestingToEventFlow y) :=
    congrArg cauchyIntervalNestingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyIntervalNesting_round_trip x).symm
      (Eq.trans hread (cauchyIntervalNesting_round_trip y)))

private theorem cauchyIntervalNesting_field_faithful :
    forall x y : CauchyIntervalNestingUp,
      cauchyIntervalNestingFields x = cauchyIntervalNestingFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 B1 N1 S1 D1 R1 E1 H1 C1 P1 L1 =>
      cases y with
      | mk I2 B2 N2 S2 D2 R2 E2 H2 C2 P2 L2 =>
          change [I1, B1, N1, S1, D1, R1, E1, H1, C1, P1, L1] =
            [I2, B2, N2, S2, D2, R2, E2, H2, C2, P2, L2] at hfields
          cases hfields
          rfl

instance cauchyIntervalNestingBHistCarrier : BHistCarrier CauchyIntervalNestingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyIntervalNestingToEventFlow
  fromEventFlow := cauchyIntervalNestingFromEventFlow

instance cauchyIntervalNestingChapterTasteGate : ChapterTasteGate CauchyIntervalNestingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyIntervalNestingFromEventFlow (cauchyIntervalNestingToEventFlow x) = some x
    exact cauchyIntervalNesting_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyIntervalNestingToEventFlow_injective heq)

instance cauchyIntervalNestingFieldFaithful : FieldFaithful CauchyIntervalNestingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyIntervalNestingFields
  field_faithful := cauchyIntervalNesting_field_faithful

instance cauchyIntervalNestingNontrivial : Nontrivial CauchyIntervalNestingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyIntervalNestingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyIntervalNestingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyIntervalNestingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyIntervalNestingDecodeBHist (cauchyIntervalNestingEncodeBHist h) = h) ∧
      (∀ x : CauchyIntervalNestingUp,
        cauchyIntervalNestingFromEventFlow (cauchyIntervalNestingToEventFlow x) = some x) ∧
        (∀ x y : CauchyIntervalNestingUp,
          cauchyIntervalNestingToEventFlow x = cauchyIntervalNestingToEventFlow y ->
            x = y) ∧
          cauchyIntervalNestingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact cauchyIntervalNestingDecodeEncode
  · constructor
    · exact cauchyIntervalNesting_round_trip
    · constructor
      · intro x y heq
        exact cauchyIntervalNestingToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyIntervalNestingUp
