import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularFilterRealizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularFilterRealizationUp : Type where
  | mk (B A G S D R E H C P N : BHist) : RegularFilterRealizationUp
  deriving DecidableEq

def regularFilterRealizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularFilterRealizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularFilterRealizationEncodeBHist h

def regularFilterRealizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularFilterRealizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularFilterRealizationDecodeBHist tail)

private theorem RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularFilterRealizationFields : RegularFilterRealizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularFilterRealizationUp.mk B A G S D R E H C P N =>
      [B, A, G, S, D, R, E, H, C, P, N]

def regularFilterRealizationToEventFlow : RegularFilterRealizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularFilterRealizationFields x).map regularFilterRealizationEncodeBHist

def regularFilterRealizationFromEventFlow :
    EventFlow → Option RegularFilterRealizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | B :: restB =>
      match restB with
      | A :: restA =>
          match restA with
          | G :: restG =>
              match restG with
              | S :: restS =>
                  match restS with
                  | D :: restD =>
                      match restD with
                      | R :: restR =>
                          match restR with
                          | E :: restE =>
                              match restE with
                              | H :: restH =>
                                  match restH with
                                  | C :: restC =>
                                      match restC with
                                      | P :: restP =>
                                          match restP with
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (RegularFilterRealizationUp.mk
                                                      (regularFilterRealizationDecodeBHist B)
                                                      (regularFilterRealizationDecodeBHist A)
                                                      (regularFilterRealizationDecodeBHist G)
                                                      (regularFilterRealizationDecodeBHist S)
                                                      (regularFilterRealizationDecodeBHist D)
                                                      (regularFilterRealizationDecodeBHist R)
                                                      (regularFilterRealizationDecodeBHist E)
                                                      (regularFilterRealizationDecodeBHist H)
                                                      (regularFilterRealizationDecodeBHist C)
                                                      (regularFilterRealizationDecodeBHist P)
                                                      (regularFilterRealizationDecodeBHist N))
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

private theorem RegularFilterRealizationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularFilterRealizationUp,
      regularFilterRealizationFromEventFlow (regularFilterRealizationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A G S D R E H C P N =>
      change
        some
          (RegularFilterRealizationUp.mk
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist B))
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist A))
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist G))
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist S))
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist D))
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist R))
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist E))
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist H))
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist C))
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist P))
            (regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist N))) =
          some (RegularFilterRealizationUp.mk B A G S D R E H C P N)
      rw [RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode B,
        RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode A,
        RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode G,
        RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode S,
        RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode D,
        RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode R,
        RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode E,
        RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode H,
        RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode C,
        RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode P,
        RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective
    {h k : BHist} :
    regularFilterRealizationEncodeBHist h = regularFilterRealizationEncodeBHist k →
      h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdec :
      regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist h) =
        regularFilterRealizationDecodeBHist (regularFilterRealizationEncodeBHist k) :=
    congrArg regularFilterRealizationDecodeBHist heq
  rw [RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode h,
    RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode k] at hdec
  exact hdec

private theorem RegularFilterRealizationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularFilterRealizationUp} :
    regularFilterRealizationToEventFlow x = regularFilterRealizationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk B₁ A₁ G₁ S₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ A₂ G₂ S₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection heq with hB tailA
          injection tailA with hA tailG
          injection tailG with hG tailS
          injection tailS with hS tailD
          injection tailD with hD tailR
          injection tailR with hR tailE
          injection tailE with hE tailH
          injection tailH with hH tailC
          injection tailC with hC tailP
          injection tailP with hP tailN
          injection tailN with hN _
          have eB :
              B₁ = B₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hB
          have eA :
              A₁ = A₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hA
          have eG :
              G₁ = G₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hG
          have eS :
              S₁ = S₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hS
          have eD :
              D₁ = D₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hD
          have eR :
              R₁ = R₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hR
          have eE :
              E₁ = E₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hE
          have eH :
              H₁ = H₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hH
          have eC :
              C₁ = C₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hC
          have eP :
              P₁ = P₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hP
          have eN :
              N₁ = N₂ :=
            RegularFilterRealizationTasteGate_single_carrier_alignment_encode_injective hN
          cases eB
          cases eA
          cases eG
          cases eS
          cases eD
          cases eR
          cases eE
          cases eH
          cases eC
          cases eP
          cases eN
          rfl

instance regularFilterRealizationBHistCarrier :
    BHistCarrier RegularFilterRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularFilterRealizationToEventFlow
  fromEventFlow := regularFilterRealizationFromEventFlow

instance regularFilterRealizationChapterTasteGate :
    ChapterTasteGate RegularFilterRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularFilterRealizationFromEventFlow (regularFilterRealizationToEventFlow x) =
        some x
    exact RegularFilterRealizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularFilterRealizationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularFilterRealizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularFilterRealizationChapterTasteGate

theorem RegularFilterRealizationTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularFilterRealizationDecodeBHist
        (regularFilterRealizationEncodeBHist h) = h) ∧
      (∀ x : RegularFilterRealizationUp,
        regularFilterRealizationFromEventFlow (regularFilterRealizationToEventFlow x) =
          some x) ∧
      (∀ x y : RegularFilterRealizationUp,
        regularFilterRealizationToEventFlow x = regularFilterRealizationToEventFlow y →
          x = y) ∧
      regularFilterRealizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularFilterRealizationTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact RegularFilterRealizationTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact RegularFilterRealizationTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.RegularFilterRealizationUp
