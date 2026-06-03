import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformConvergenceTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformConvergenceTestUp : Type where
  | mk (F S N T M R E H C P Q : BHist) : UniformConvergenceTestUp
  deriving DecidableEq

def uniformConvergenceTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformConvergenceTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformConvergenceTestEncodeBHist h

def uniformConvergenceTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformConvergenceTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformConvergenceTestDecodeBHist tail)

private theorem UniformConvergenceTestTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformConvergenceTestDecodeBHist (uniformConvergenceTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem uniformConvergenceTest_mk_congr
    {F F' S S' N N' T T' M M' R R' E E' H H' C C' P P' Q Q' : BHist}
    (hF : F' = F) (hS : S' = S) (hN : N' = N) (hT : T' = T)
    (hM : M' = M) (hR : R' = R) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hQ : Q' = Q) :
    UniformConvergenceTestUp.mk F' S' N' T' M' R' E' H' C' P' Q' =
      UniformConvergenceTestUp.mk F S N T M R E H C P Q := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hS
  cases hN
  cases hT
  cases hM
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hQ
  rfl

def uniformConvergenceTestToEventFlow : UniformConvergenceTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformConvergenceTestUp.mk F S N T M R E H C P Q =>
      [uniformConvergenceTestEncodeBHist F,
        uniformConvergenceTestEncodeBHist S,
        uniformConvergenceTestEncodeBHist N,
        uniformConvergenceTestEncodeBHist T,
        uniformConvergenceTestEncodeBHist M,
        uniformConvergenceTestEncodeBHist R,
        uniformConvergenceTestEncodeBHist E,
        uniformConvergenceTestEncodeBHist H,
        uniformConvergenceTestEncodeBHist C,
        uniformConvergenceTestEncodeBHist P,
        uniformConvergenceTestEncodeBHist Q]

def uniformConvergenceTestFromEventFlow : EventFlow → Option UniformConvergenceTestUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: restF =>
      match restF with
      | S :: restS =>
          match restS with
          | N :: restN =>
              match restN with
              | T :: restT =>
                  match restT with
                  | M :: restM =>
                      match restM with
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
                                          | Q :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (UniformConvergenceTestUp.mk
                                                      (uniformConvergenceTestDecodeBHist F)
                                                      (uniformConvergenceTestDecodeBHist S)
                                                      (uniformConvergenceTestDecodeBHist N)
                                                      (uniformConvergenceTestDecodeBHist T)
                                                      (uniformConvergenceTestDecodeBHist M)
                                                      (uniformConvergenceTestDecodeBHist R)
                                                      (uniformConvergenceTestDecodeBHist E)
                                                      (uniformConvergenceTestDecodeBHist H)
                                                      (uniformConvergenceTestDecodeBHist C)
                                                      (uniformConvergenceTestDecodeBHist P)
                                                      (uniformConvergenceTestDecodeBHist Q))
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

private theorem UniformConvergenceTestTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformConvergenceTestUp,
      uniformConvergenceTestFromEventFlow
        (uniformConvergenceTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S N T M R E H C P Q =>
      exact
        congrArg some
          (uniformConvergenceTest_mk_congr
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode F)
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode S)
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode N)
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode T)
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode M)
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode R)
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode E)
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode H)
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode C)
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode P)
            (UniformConvergenceTestTasteGate_single_carrier_alignment_decode Q))

private theorem UniformConvergenceTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformConvergenceTestUp} :
    uniformConvergenceTestToEventFlow x = uniformConvergenceTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformConvergenceTestFromEventFlow (uniformConvergenceTestToEventFlow x) =
        uniformConvergenceTestFromEventFlow (uniformConvergenceTestToEventFlow y) :=
    congrArg uniformConvergenceTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformConvergenceTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformConvergenceTestTasteGate_single_carrier_alignment_round_trip y)))

instance uniformConvergenceTestBHistCarrier :
    BHistCarrier UniformConvergenceTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformConvergenceTestToEventFlow
  fromEventFlow := uniformConvergenceTestFromEventFlow

instance uniformConvergenceTestChapterTasteGate :
    ChapterTasteGate UniformConvergenceTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformConvergenceTestFromEventFlow
        (uniformConvergenceTestToEventFlow x) = some x
    exact UniformConvergenceTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformConvergenceTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniformConvergenceTestTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformConvergenceTestUp) ∧
      (∀ h : BHist,
        uniformConvergenceTestDecodeBHist (uniformConvergenceTestEncodeBHist h) = h) ∧
      (∀ x : UniformConvergenceTestUp,
        uniformConvergenceTestFromEventFlow
          (uniformConvergenceTestToEventFlow x) = some x) ∧
      uniformConvergenceTestEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact
      ⟨{
        round_trip := by
          intro x
          change
            uniformConvergenceTestFromEventFlow
              (uniformConvergenceTestToEventFlow x) = some x
          exact UniformConvergenceTestTasteGate_single_carrier_alignment_round_trip x
        layer_separation := by
          intro x y hxy heq
          exact hxy (UniformConvergenceTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)
      }⟩
  constructor
  · exact UniformConvergenceTestTasteGate_single_carrier_alignment_decode
  constructor
  · exact UniformConvergenceTestTasteGate_single_carrier_alignment_round_trip
  · rfl

end BEDC.Derived.UniformConvergenceTestUp
