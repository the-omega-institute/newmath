import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopIntervalCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopIntervalCompletionUp : Type where
  | mk :
      (I S Q D E L U A R T H C P N : BHist) →
        BishopIntervalCompletionUp
  deriving DecidableEq

def bishopIntervalCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopIntervalCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopIntervalCompletionEncodeBHist h

def bishopIntervalCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopIntervalCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopIntervalCompletionDecodeBHist tail)

private theorem BishopIntervalCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopIntervalCompletionDecodeBHist
        (bishopIntervalCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopIntervalCompletionFields : BishopIntervalCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalCompletionUp.mk I S Q D E L U A R T H C P N =>
      [I, S, Q, D, E, L, U, A, R, T, H, C, P, N]

def bishopIntervalCompletionToEventFlow : BishopIntervalCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopIntervalCompletionFields x).map bishopIntervalCompletionEncodeBHist

def bishopIntervalCompletionFromEventFlow :
    EventFlow → Option BishopIntervalCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | I :: restI =>
      match restI with
      | S :: restS =>
          match restS with
          | Q :: restQ =>
              match restQ with
              | D :: restD =>
                  match restD with
                  | E :: restE =>
                      match restE with
                      | L :: restL =>
                          match restL with
                          | U :: restU =>
                              match restU with
                              | A :: restA =>
                                  match restA with
                                  | R :: restR =>
                                      match restR with
                                      | T :: restT =>
                                          match restT with
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
                                                                (BishopIntervalCompletionUp.mk
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    I)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    S)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    Q)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    D)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    E)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    L)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    U)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    A)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    R)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    T)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    H)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    C)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    P)
                                                                  (bishopIntervalCompletionDecodeBHist
                                                                    N))
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
      | [] => none
  | [] => none

private theorem bishopIntervalCompletion_mk_congr
    {I I' S S' Q Q' D D' E E' L L' U U' A A' R R' T T' H H' C C' P P' N N' :
      BHist}
    (hI : I' = I) (hS : S' = S) (hQ : Q' = Q) (hD : D' = D)
    (hE : E' = E) (hL : L' = L) (hU : U' = U) (hA : A' = A)
    (hR : R' = R) (hT : T' = T) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    BishopIntervalCompletionUp.mk I' S' Q' D' E' L' U' A' R' T' H' C' P' N' =
      BishopIntervalCompletionUp.mk I S Q D E L U A R T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hS
  cases hQ
  cases hD
  cases hE
  cases hL
  cases hU
  cases hA
  cases hR
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem BishopIntervalCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopIntervalCompletionUp,
      bishopIntervalCompletionFromEventFlow
        (bishopIntervalCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S Q D E L U A R T H C P N =>
      exact
        congrArg some
          (bishopIntervalCompletion_mk_congr
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode I)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode S)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode Q)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode D)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode E)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode L)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode U)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode A)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode R)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode T)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode H)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode C)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode P)
            (BishopIntervalCompletionTasteGate_single_carrier_alignment_decode N))

private theorem BishopIntervalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopIntervalCompletionUp} :
    bishopIntervalCompletionToEventFlow x =
      bishopIntervalCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopIntervalCompletionFromEventFlow
          (bishopIntervalCompletionToEventFlow x) =
        bishopIntervalCompletionFromEventFlow
          (bishopIntervalCompletionToEventFlow y) :=
    congrArg bishopIntervalCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopIntervalCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopIntervalCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopIntervalCompletionBHistCarrier :
    BHistCarrier BishopIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopIntervalCompletionToEventFlow
  fromEventFlow := bishopIntervalCompletionFromEventFlow

instance bishopIntervalCompletionChapterTasteGate :
    ChapterTasteGate BishopIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopIntervalCompletionFromEventFlow
        (bishopIntervalCompletionToEventFlow x) = some x
    exact BishopIntervalCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopIntervalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopIntervalCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopIntervalCompletionDecodeBHist
        (bishopIntervalCompletionEncodeBHist h) = h) ∧
      (∀ x : BishopIntervalCompletionUp,
        bishopIntervalCompletionFromEventFlow
          (bishopIntervalCompletionToEventFlow x) = some x) ∧
        (∀ x y : BishopIntervalCompletionUp,
          bishopIntervalCompletionToEventFlow x =
            bishopIntervalCompletionToEventFlow y → x = y) ∧
          bishopIntervalCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopIntervalCompletionTasteGate_single_carrier_alignment_decode,
      BishopIntervalCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopIntervalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopIntervalCompletionUp
