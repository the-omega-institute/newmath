import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DirichletFunctionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DirichletFunctionUp : Type where
  | mk (R Delta I W G A H C P N : BHist) : DirichletFunctionUp
  deriving DecidableEq

def dirichletFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dirichletFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dirichletFunctionEncodeBHist h

def dirichletFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dirichletFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dirichletFunctionDecodeBHist tail)

private theorem DirichletFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dirichletFunctionFields : DirichletFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DirichletFunctionUp.mk R Delta I W G A H C P N =>
      [R, Delta, I, W, G, A, H, C, P, N]

def dirichletFunctionToEventFlow : DirichletFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dirichletFunctionFields x).map dirichletFunctionEncodeBHist

def dirichletFunctionFromEventFlow : EventFlow → Option DirichletFunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | Delta :: rest1 =>
          match rest1 with
          | [] => none
          | I :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | G :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (DirichletFunctionUp.mk
                                                  (dirichletFunctionDecodeBHist R)
                                                  (dirichletFunctionDecodeBHist Delta)
                                                  (dirichletFunctionDecodeBHist I)
                                                  (dirichletFunctionDecodeBHist W)
                                                  (dirichletFunctionDecodeBHist G)
                                                  (dirichletFunctionDecodeBHist A)
                                                  (dirichletFunctionDecodeBHist H)
                                                  (dirichletFunctionDecodeBHist C)
                                                  (dirichletFunctionDecodeBHist P)
                                                  (dirichletFunctionDecodeBHist N))
                                          | _ :: _ => none

private theorem DirichletFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DirichletFunctionUp,
      dirichletFunctionFromEventFlow (dirichletFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R Delta I W G A H C P N =>
      change
        some
          (DirichletFunctionUp.mk
            (dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist R))
            (dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist Delta))
            (dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist I))
            (dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist W))
            (dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist G))
            (dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist A))
            (dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist H))
            (dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist C))
            (dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist P))
            (dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist N))) =
          some (DirichletFunctionUp.mk R Delta I W G A H C P N)
      rw [DirichletFunctionTasteGate_single_carrier_alignment_decode_encode R]
      rw [DirichletFunctionTasteGate_single_carrier_alignment_decode_encode Delta]
      rw [DirichletFunctionTasteGate_single_carrier_alignment_decode_encode I]
      rw [DirichletFunctionTasteGate_single_carrier_alignment_decode_encode W]
      rw [DirichletFunctionTasteGate_single_carrier_alignment_decode_encode G]
      rw [DirichletFunctionTasteGate_single_carrier_alignment_decode_encode A]
      rw [DirichletFunctionTasteGate_single_carrier_alignment_decode_encode H]
      rw [DirichletFunctionTasteGate_single_carrier_alignment_decode_encode C]
      rw [DirichletFunctionTasteGate_single_carrier_alignment_decode_encode P]
      rw [DirichletFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem DirichletFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DirichletFunctionUp} :
    dirichletFunctionToEventFlow x = dirichletFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have roundX := DirichletFunctionTasteGate_single_carrier_alignment_round_trip x
  have roundY := DirichletFunctionTasteGate_single_carrier_alignment_round_trip y
  rw [heq] at roundX
  rw [roundY] at roundX
  exact Option.some.inj roundX.symm

instance dirichletFunctionBHistCarrier : BHistCarrier DirichletFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dirichletFunctionToEventFlow
  fromEventFlow := dirichletFunctionFromEventFlow

instance dirichletFunctionChapterTasteGate : ChapterTasteGate DirichletFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := DirichletFunctionTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (DirichletFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DirichletFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dirichletFunctionChapterTasteGate

theorem DirichletFunctionTasteGate_single_carrier_alignment :
    (forall h : BHist, dirichletFunctionDecodeBHist (dirichletFunctionEncodeBHist h) = h) ∧
      (forall x : DirichletFunctionUp,
        dirichletFunctionFromEventFlow (dirichletFunctionToEventFlow x) = some x) ∧
        (forall x y : DirichletFunctionUp,
          dirichletFunctionToEventFlow x = dirichletFunctionToEventFlow y -> x = y) ∧
          dirichletFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DirichletFunctionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact DirichletFunctionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact DirichletFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.DirichletFunctionUp.TasteGate
