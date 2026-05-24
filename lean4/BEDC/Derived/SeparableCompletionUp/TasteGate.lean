import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparableCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparableCompletionUp : Type where
  | mk (M D C W T R E H P N : BHist) : SeparableCompletionUp
  deriving DecidableEq

def separableCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separableCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separableCompletionEncodeBHist h

def separableCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separableCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separableCompletionDecodeBHist tail)

private theorem SeparableCompletionUp_single_carrier_alignment_decode :
    ∀ h : BHist, separableCompletionDecodeBHist (separableCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separableCompletionFields : SeparableCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparableCompletionUp.mk M D C W T R E H P N => [M, D, C, W, T, R, E, H, P, N]

def separableCompletionToEventFlow : SeparableCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (separableCompletionFields x).map separableCompletionEncodeBHist

def separableCompletionFromEventFlow : EventFlow → Option SeparableCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: restM =>
      match restM with
      | D :: restD =>
          match restD with
          | C :: restC =>
              match restC with
              | W :: restW =>
                  match restW with
                  | T :: restT =>
                      match restT with
                      | R :: restR =>
                          match restR with
                          | E :: restE =>
                              match restE with
                              | H :: restH =>
                                  match restH with
                                  | P :: restP =>
                                      match restP with
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (SeparableCompletionUp.mk
                                                  (separableCompletionDecodeBHist M)
                                                  (separableCompletionDecodeBHist D)
                                                  (separableCompletionDecodeBHist C)
                                                  (separableCompletionDecodeBHist W)
                                                  (separableCompletionDecodeBHist T)
                                                  (separableCompletionDecodeBHist R)
                                                  (separableCompletionDecodeBHist E)
                                                  (separableCompletionDecodeBHist H)
                                                  (separableCompletionDecodeBHist P)
                                                  (separableCompletionDecodeBHist N))
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

private theorem separableCompletion_mk_congr
    {M M' D D' C C' W W' T T' R R' E E' H H' P P' N N' : BHist}
    (hM : M' = M) (hD : D' = D) (hC : C' = C) (hW : W' = W)
    (hT : T' = T) (hR : R' = R) (hE : E' = E) (hH : H' = H)
    (hP : P' = P) (hN : N' = N) :
    SeparableCompletionUp.mk M' D' C' W' T' R' E' H' P' N' =
      SeparableCompletionUp.mk M D C W T R E H P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hD
  cases hC
  cases hW
  cases hT
  cases hR
  cases hE
  cases hH
  cases hP
  cases hN
  rfl

private theorem SeparableCompletionUp_single_carrier_alignment_round_trip :
    ∀ x : SeparableCompletionUp,
      separableCompletionFromEventFlow (separableCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D C W T R E H P N =>
      exact congrArg some
        (separableCompletion_mk_congr
          (SeparableCompletionUp_single_carrier_alignment_decode M)
          (SeparableCompletionUp_single_carrier_alignment_decode D)
          (SeparableCompletionUp_single_carrier_alignment_decode C)
          (SeparableCompletionUp_single_carrier_alignment_decode W)
          (SeparableCompletionUp_single_carrier_alignment_decode T)
          (SeparableCompletionUp_single_carrier_alignment_decode R)
          (SeparableCompletionUp_single_carrier_alignment_decode E)
          (SeparableCompletionUp_single_carrier_alignment_decode H)
          (SeparableCompletionUp_single_carrier_alignment_decode P)
          (SeparableCompletionUp_single_carrier_alignment_decode N))

private theorem separableCompletionToEventFlow_injective {x y : SeparableCompletionUp} :
    separableCompletionToEventFlow x = separableCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separableCompletionFromEventFlow (separableCompletionToEventFlow x) =
        separableCompletionFromEventFlow (separableCompletionToEventFlow y) :=
    congrArg separableCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SeparableCompletionUp_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SeparableCompletionUp_single_carrier_alignment_round_trip y)))

instance separableCompletionBHistCarrier : BHistCarrier SeparableCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separableCompletionToEventFlow
  fromEventFlow := separableCompletionFromEventFlow

instance separableCompletionChapterTasteGate :
    ChapterTasteGate SeparableCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change separableCompletionFromEventFlow (separableCompletionToEventFlow x) = some x
    exact SeparableCompletionUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (separableCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SeparableCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separableCompletionChapterTasteGate

theorem SeparableCompletionUp_single_carrier_alignment :
    (∀ h : BHist, separableCompletionDecodeBHist (separableCompletionEncodeBHist h) = h) ∧
      (∀ x : SeparableCompletionUp,
        separableCompletionFromEventFlow (separableCompletionToEventFlow x) = some x) ∧
      (∀ x y : SeparableCompletionUp,
        separableCompletionToEventFlow x = separableCompletionToEventFlow y → x = y) ∧
      separableCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SeparableCompletionUp_single_carrier_alignment_decode
  constructor
  · exact SeparableCompletionUp_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact separableCompletionToEventFlow_injective heq
  · rfl

end BEDC.Derived.SeparableCompletionUp
