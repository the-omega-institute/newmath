import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalConvergenceBoundUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalConvergenceBoundUp : Type where
  | mk (X mu n D Q R E H C P N : BHist) : DiagonalConvergenceBoundUp
  deriving DecidableEq

def diagonalConvergenceBoundEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalConvergenceBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalConvergenceBoundEncodeBHist h

def diagonalConvergenceBoundDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalConvergenceBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalConvergenceBoundDecodeBHist tail)

private theorem DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      diagonalConvergenceBoundDecodeBHist (diagonalConvergenceBoundEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diagonalConvergenceBoundFields : DiagonalConvergenceBoundUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalConvergenceBoundUp.mk X mu n D Q R E H C P N => [X, mu, n, D, Q, R, E, H, C, P, N]

def diagonalConvergenceBoundToEventFlow : DiagonalConvergenceBoundUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (diagonalConvergenceBoundFields x).map diagonalConvergenceBoundEncodeBHist

def diagonalConvergenceBoundFromEventFlow : EventFlow → Option DiagonalConvergenceBoundUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | mu :: restMu =>
          match restMu with
          | n :: restN =>
              match restN with
              | D :: restD =>
                  match restD with
                  | Q :: restQ =>
                      match restQ with
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
                                                    (DiagonalConvergenceBoundUp.mk
                                                      (diagonalConvergenceBoundDecodeBHist X)
                                                      (diagonalConvergenceBoundDecodeBHist mu)
                                                      (diagonalConvergenceBoundDecodeBHist n)
                                                      (diagonalConvergenceBoundDecodeBHist D)
                                                      (diagonalConvergenceBoundDecodeBHist Q)
                                                      (diagonalConvergenceBoundDecodeBHist R)
                                                      (diagonalConvergenceBoundDecodeBHist E)
                                                      (diagonalConvergenceBoundDecodeBHist H)
                                                      (diagonalConvergenceBoundDecodeBHist C)
                                                      (diagonalConvergenceBoundDecodeBHist P)
                                                      (diagonalConvergenceBoundDecodeBHist N))
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

private theorem diagonalConvergenceBound_mk_congr
    {X X' mu mu' n n' D D' Q Q' R R' E E' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hmu : mu' = mu) (hn : n' = n) (hD : D' = D)
    (hQ : Q' = Q) (hR : R' = R) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    DiagonalConvergenceBoundUp.mk X' mu' n' D' Q' R' E' H' C' P' N' =
      DiagonalConvergenceBoundUp.mk X mu n D Q R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hmu
  cases hn
  cases hD
  cases hQ
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem DiagonalConvergenceBoundTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DiagonalConvergenceBoundUp,
      diagonalConvergenceBoundFromEventFlow (diagonalConvergenceBoundToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X mu n D Q R E H C P N =>
      exact
        congrArg some
          (diagonalConvergenceBound_mk_congr
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode X)
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode mu)
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode n)
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode D)
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode Q)
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode R)
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode E)
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode H)
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode C)
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode P)
            (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode N))

private theorem diagonalConvergenceBoundToEventFlow_injective
    {x y : DiagonalConvergenceBoundUp} :
    diagonalConvergenceBoundToEventFlow x = diagonalConvergenceBoundToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalConvergenceBoundFromEventFlow (diagonalConvergenceBoundToEventFlow x) =
        diagonalConvergenceBoundFromEventFlow (diagonalConvergenceBoundToEventFlow y) :=
    congrArg diagonalConvergenceBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DiagonalConvergenceBoundTasteGate_single_carrier_alignment_round_trip y)))

private theorem diagonalConvergenceBound_field_faithful :
    ∀ x y : DiagonalConvergenceBoundUp,
      diagonalConvergenceBoundFields x = diagonalConvergenceBoundFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X mu n D Q R E H C P N =>
      cases y with
      | mk X' mu' n' D' Q' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance diagonalConvergenceBoundBHistCarrier : BHistCarrier DiagonalConvergenceBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalConvergenceBoundToEventFlow
  fromEventFlow := diagonalConvergenceBoundFromEventFlow

instance diagonalConvergenceBoundChapterTasteGate :
    ChapterTasteGate DiagonalConvergenceBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diagonalConvergenceBoundFromEventFlow (diagonalConvergenceBoundToEventFlow x) = some x
    exact DiagonalConvergenceBoundTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diagonalConvergenceBoundToEventFlow_injective heq)

instance diagonalConvergenceBoundFieldFaithful : FieldFaithful DiagonalConvergenceBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diagonalConvergenceBoundFields
  field_faithful := diagonalConvergenceBound_field_faithful

instance diagonalConvergenceBoundNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DiagonalConvergenceBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiagonalConvergenceBoundUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiagonalConvergenceBoundUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DiagonalConvergenceBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diagonalConvergenceBoundChapterTasteGate

theorem DiagonalConvergenceBoundTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DiagonalConvergenceBoundUp) ∧
      Nonempty (FieldFaithful DiagonalConvergenceBoundUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial DiagonalConvergenceBoundUp) ∧
      (∀ h : BHist,
        diagonalConvergenceBoundDecodeBHist (diagonalConvergenceBoundEncodeBHist h) = h) ∧
      (∀ x : DiagonalConvergenceBoundUp,
        diagonalConvergenceBoundFromEventFlow (diagonalConvergenceBoundToEventFlow x) = some x) ∧
      (∀ x y : DiagonalConvergenceBoundUp,
        diagonalConvergenceBoundToEventFlow x = diagonalConvergenceBoundToEventFlow y → x = y) ∧
      diagonalConvergenceBoundEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨diagonalConvergenceBoundChapterTasteGate⟩
  constructor
  · exact ⟨diagonalConvergenceBoundFieldFaithful⟩
  constructor
  · exact ⟨diagonalConvergenceBoundNontrivial⟩
  constructor
  · exact DiagonalConvergenceBoundTasteGate_single_carrier_alignment_decode
  constructor
  · exact DiagonalConvergenceBoundTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact diagonalConvergenceBoundToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.DiagonalConvergenceBoundUp
