import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopFanModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopFanModulusUp : Type where
  | mk (F A B S Q D R U H C P N : BHist) : BishopFanModulusUp
  deriving DecidableEq

def bishopFanModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopFanModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopFanModulusEncodeBHist h

def bishopFanModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopFanModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopFanModulusDecodeBHist tail)

private theorem BishopFanModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem BishopFanModulusTasteGate_single_carrier_alignment_mk_congr
    {F1 A1 B1 S1 Q1 D1 R1 U1 H1 C1 P1 N1 F2 A2 B2 S2 Q2 D2 R2 U2 H2 C2 P2 N2 :
      BHist}
    (hF : F1 = F2)
    (hA : A1 = A2)
    (hB : B1 = B2)
    (hS : S1 = S2)
    (hQ : Q1 = Q2)
    (hD : D1 = D2)
    (hR : R1 = R2)
    (hU : U1 = U2)
    (hH : H1 = H2)
    (hC : C1 = C2)
    (hP : P1 = P2)
    (hN : N1 = N2) :
    BishopFanModulusUp.mk F1 A1 B1 S1 Q1 D1 R1 U1 H1 C1 P1 N1 =
      BishopFanModulusUp.mk F2 A2 B2 S2 Q2 D2 R2 U2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hA
  cases hB
  cases hS
  cases hQ
  cases hD
  cases hR
  cases hU
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def bishopFanModulusToEventFlow : BishopFanModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopFanModulusUp.mk F A B S Q D R U H C P N =>
      [[BMark.b0],
        bishopFanModulusEncodeBHist F,
        [BMark.b1, BMark.b0],
        bishopFanModulusEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        bishopFanModulusEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopFanModulusEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopFanModulusEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopFanModulusEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopFanModulusEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bishopFanModulusEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bishopFanModulusEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bishopFanModulusEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopFanModulusEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopFanModulusEncodeBHist N]

def bishopFanModulusPayloads : EventFlow → Option EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some []
  | _ :: rest =>
      match rest with
      | [] => none
      | row :: tail =>
          match bishopFanModulusPayloads tail with
          | some rows => some (row :: rows)
          | none => none

def bishopFanModulusFromPayloads : EventFlow → Option BishopFanModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: restA =>
      match restA with
      | [] => none
      | A :: restB =>
          match restB with
          | [] => none
          | B :: restS =>
              match restS with
              | [] => none
              | S :: restQ =>
                  match restQ with
                  | [] => none
                  | Q :: restD =>
                      match restD with
                      | [] => none
                      | D :: restR =>
                          match restR with
                          | [] => none
                          | R :: restU =>
                              match restU with
                              | [] => none
                              | U :: restH =>
                                  match restH with
                                  | [] => none
                                  | H :: restC =>
                                      match restC with
                                      | [] => none
                                      | C :: restP =>
                                          match restP with
                                          | [] => none
                                          | P :: restN =>
                                              match restN with
                                              | [] => none
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some (BishopFanModulusUp.mk
                                                        (bishopFanModulusDecodeBHist F)
                                                        (bishopFanModulusDecodeBHist A)
                                                        (bishopFanModulusDecodeBHist B)
                                                        (bishopFanModulusDecodeBHist S)
                                                        (bishopFanModulusDecodeBHist Q)
                                                        (bishopFanModulusDecodeBHist D)
                                                        (bishopFanModulusDecodeBHist R)
                                                        (bishopFanModulusDecodeBHist U)
                                                        (bishopFanModulusDecodeBHist H)
                                                        (bishopFanModulusDecodeBHist C)
                                                        (bishopFanModulusDecodeBHist P)
                                                        (bishopFanModulusDecodeBHist N))
                                                  | _ :: _ => none

def bishopFanModulusFromEventFlow
    (flow : EventFlow) : Option BishopFanModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match bishopFanModulusPayloads flow with
  | some rows => bishopFanModulusFromPayloads rows
  | none => none

private theorem BishopFanModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopFanModulusUp,
      bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F A B S Q D R U H C P N =>
      change
        some
          (BishopFanModulusUp.mk
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist F))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist A))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist B))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist S))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist Q))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist D))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist R))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist U))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist H))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist C))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist P))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist N))) =
          some (BishopFanModulusUp.mk F A B S Q D R U H C P N)
      exact congrArg some
        (BishopFanModulusTasteGate_single_carrier_alignment_mk_congr
          (BishopFanModulusTasteGate_single_carrier_alignment_decode F)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode A)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode B)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode S)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode Q)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode D)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode R)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode U)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode H)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode C)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode P)
          (BishopFanModulusTasteGate_single_carrier_alignment_decode N))

private theorem BishopFanModulusTasteGate_single_carrier_alignment_injective
    {x y : BishopFanModulusUp} :
    bishopFanModulusToEventFlow x = bishopFanModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) =
        bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow y) :=
    congrArg bishopFanModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopFanModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopFanModulusTasteGate_single_carrier_alignment_round_trip y)))

instance bishopFanModulusBHistCarrier : BHistCarrier BishopFanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopFanModulusToEventFlow
  fromEventFlow := bishopFanModulusFromEventFlow

instance bishopFanModulusChapterTasteGate : ChapterTasteGate BishopFanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) = some x
    exact BishopFanModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopFanModulusTasteGate_single_carrier_alignment_injective heq)

theorem BishopFanModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist h) = h) ∧
      (∀ x : BishopFanModulusUp,
        bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) = some x) ∧
      (∀ x y : BishopFanModulusUp,
        bishopFanModulusToEventFlow x = bishopFanModulusToEventFlow y → x = y) ∧
      bishopFanModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro BishopFanModulusTasteGate_single_carrier_alignment_decode
      (And.intro BishopFanModulusTasteGate_single_carrier_alignment_round_trip
        (And.intro
          (fun x y heq => BishopFanModulusTasteGate_single_carrier_alignment_injective heq)
          rfl))

end BEDC.Derived.BishopFanModulusUp
