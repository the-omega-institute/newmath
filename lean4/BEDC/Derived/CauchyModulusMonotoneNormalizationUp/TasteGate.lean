import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusMonotoneNormalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusMonotoneNormalizationUp : Type where
  | mk (S M D T U W E H C P N : BHist) :
      CauchyModulusMonotoneNormalizationUp
  deriving DecidableEq

def cauchyModulusMonotoneNormalizationFields :
    CauchyModulusMonotoneNormalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusMonotoneNormalizationUp.mk S M D T U W E H C P N =>
      [S, M, D, T, U, W, E, H, C, P, N]

def cauchyModulusMonotoneNormalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusMonotoneNormalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusMonotoneNormalizationEncodeBHist h

def cauchyModulusMonotoneNormalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusMonotoneNormalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusMonotoneNormalizationDecodeBHist tail)

private theorem cauchyModulusMonotoneNormalization_decode_encode_bhist :
    ∀ h : BHist,
      cauchyModulusMonotoneNormalizationDecodeBHist
          (cauchyModulusMonotoneNormalizationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyModulusMonotoneNormalization_eq_of_encode_eq
    {h k : BHist}
    (heq :
      cauchyModulusMonotoneNormalizationEncodeBHist h =
        cauchyModulusMonotoneNormalizationEncodeBHist k) :
    h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    Eq.trans (cauchyModulusMonotoneNormalization_decode_encode_bhist h).symm
      (Eq.trans (congrArg cauchyModulusMonotoneNormalizationDecodeBHist heq)
        (cauchyModulusMonotoneNormalization_decode_encode_bhist k))

private theorem cauchyModulusMonotoneNormalization_mk_congr
    {S S' M M' D D' T T' U U' W W' E E' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hM : M' = M) (hD : D' = D) (hT : T' = T)
    (hU : U' = U) (hW : W' = W) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyModulusMonotoneNormalizationUp.mk S' M' D' T' U' W' E' H' C' P' N' =
      CauchyModulusMonotoneNormalizationUp.mk S M D T U W E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hM
  cases hD
  cases hT
  cases hU
  cases hW
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyModulusMonotoneNormalizationToEventFlow :
    CauchyModulusMonotoneNormalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusMonotoneNormalizationUp.mk S M D T U W E H C P N =>
      [cauchyModulusMonotoneNormalizationEncodeBHist S,
        cauchyModulusMonotoneNormalizationEncodeBHist M,
        cauchyModulusMonotoneNormalizationEncodeBHist D,
        cauchyModulusMonotoneNormalizationEncodeBHist T,
        cauchyModulusMonotoneNormalizationEncodeBHist U,
        cauchyModulusMonotoneNormalizationEncodeBHist W,
        cauchyModulusMonotoneNormalizationEncodeBHist E,
        cauchyModulusMonotoneNormalizationEncodeBHist H,
        cauchyModulusMonotoneNormalizationEncodeBHist C,
        cauchyModulusMonotoneNormalizationEncodeBHist P,
        cauchyModulusMonotoneNormalizationEncodeBHist N]

private def cauchyModulusMonotoneNormalizationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyModulusMonotoneNormalizationEventAtDefault index rest

def cauchyModulusMonotoneNormalizationFromEventFlow :
    EventFlow → Option CauchyModulusMonotoneNormalizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: restS =>
      match restS with
      | [] => none
      | M :: restM =>
          match restM with
          | [] => none
          | D :: restD =>
              match restD with
              | [] => none
              | T :: restT =>
                  match restT with
                  | [] => none
                  | U :: restU =>
                      match restU with
                      | [] => none
                      | W :: restW =>
                          match restW with
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
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (CauchyModulusMonotoneNormalizationUp.mk
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist S)
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist M)
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist D)
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist T)
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist U)
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist W)
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist E)
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist H)
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist C)
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist P)
                                                      (cauchyModulusMonotoneNormalizationDecodeBHist N))
                                              | _ :: _ => none

private theorem cauchyModulusMonotoneNormalization_round_trip :
    ∀ x : CauchyModulusMonotoneNormalizationUp,
      cauchyModulusMonotoneNormalizationFromEventFlow
          (cauchyModulusMonotoneNormalizationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M D T U W E H C P N =>
      exact
        Eq.ndrec
          (motive := fun z =>
            some
                (CauchyModulusMonotoneNormalizationUp.mk
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist S))
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist M))
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist D))
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist T))
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist U))
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist W))
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist E))
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist H))
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist C))
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist P))
                  (cauchyModulusMonotoneNormalizationDecodeBHist
                    (cauchyModulusMonotoneNormalizationEncodeBHist N))) =
              some z)
          rfl
          (cauchyModulusMonotoneNormalization_mk_congr
          (cauchyModulusMonotoneNormalization_decode_encode_bhist S)
          (cauchyModulusMonotoneNormalization_decode_encode_bhist M)
          (cauchyModulusMonotoneNormalization_decode_encode_bhist D)
          (cauchyModulusMonotoneNormalization_decode_encode_bhist T)
          (cauchyModulusMonotoneNormalization_decode_encode_bhist U)
          (cauchyModulusMonotoneNormalization_decode_encode_bhist W)
          (cauchyModulusMonotoneNormalization_decode_encode_bhist E)
          (cauchyModulusMonotoneNormalization_decode_encode_bhist H)
          (cauchyModulusMonotoneNormalization_decode_encode_bhist C)
          (cauchyModulusMonotoneNormalization_decode_encode_bhist P)
          (cauchyModulusMonotoneNormalization_decode_encode_bhist N))

private theorem cauchyModulusMonotoneNormalizationToEventFlow_injective
    {x y : CauchyModulusMonotoneNormalizationUp} :
    cauchyModulusMonotoneNormalizationToEventFlow x =
      cauchyModulusMonotoneNormalizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk S M D T U W E H C P N =>
      cases y with
      | mk S' M' D' T' U' W' E' H' C' P' N' =>
          have hS' :
              S = S' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 0) heq)
          have hM' :
              M = M' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 1) heq)
          have hD' :
              D = D' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 2) heq)
          have hT' :
              T = T' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 3) heq)
          have hU' :
              U = U' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 4) heq)
          have hW' :
              W = W' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 5) heq)
          have hE' :
              E = E' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 6) heq)
          have hH' :
              H = H' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 7) heq)
          have hC' :
              C = C' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 8) heq)
          have hP' :
              P = P' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 9) heq)
          have hN' :
              N = N' := by
            exact cauchyModulusMonotoneNormalization_eq_of_encode_eq
              (congrArg (cauchyModulusMonotoneNormalizationEventAtDefault 10) heq)
          cases hS'
          cases hM'
          cases hD'
          cases hT'
          cases hU'
          cases hW'
          cases hE'
          cases hH'
          cases hC'
          cases hP'
          cases hN'
          rfl

instance cauchyModulusMonotoneNormalizationBHistCarrier :
    BHistCarrier CauchyModulusMonotoneNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusMonotoneNormalizationToEventFlow
  fromEventFlow := cauchyModulusMonotoneNormalizationFromEventFlow

instance cauchyModulusMonotoneNormalizationChapterTasteGate :
    ChapterTasteGate CauchyModulusMonotoneNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyModulusMonotoneNormalizationFromEventFlow
        (cauchyModulusMonotoneNormalizationToEventFlow x) = some x
    exact cauchyModulusMonotoneNormalization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusMonotoneNormalizationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyModulusMonotoneNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusMonotoneNormalizationChapterTasteGate

theorem CauchyModulusMonotoneNormalizationUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cauchyModulusMonotoneNormalizationDecodeBHist
            (cauchyModulusMonotoneNormalizationEncodeBHist h) =
          h) ∧
      (∀ x : CauchyModulusMonotoneNormalizationUp,
        cauchyModulusMonotoneNormalizationFromEventFlow
            (cauchyModulusMonotoneNormalizationToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyModulusMonotoneNormalizationUp,
        cauchyModulusMonotoneNormalizationToEventFlow x =
          cauchyModulusMonotoneNormalizationToEventFlow y →
            x = y) ∧
      cauchyModulusMonotoneNormalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyModulusMonotoneNormalization_decode_encode_bhist
  · constructor
    · exact cauchyModulusMonotoneNormalization_round_trip
    · constructor
      · intro x y
        exact cauchyModulusMonotoneNormalizationToEventFlow_injective
      · rfl

end BEDC.Derived.CauchyModulusMonotoneNormalizationUp
