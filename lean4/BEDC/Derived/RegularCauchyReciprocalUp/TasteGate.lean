import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyReciprocalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyReciprocalUp : Type where
  | mk (Q A M W D B T E H C P N : BHist) : RegularCauchyReciprocalUp
  deriving DecidableEq

def regularCauchyReciprocalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyReciprocalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyReciprocalEncodeBHist h

def regularCauchyReciprocalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyReciprocalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyReciprocalDecodeBHist tail)

private theorem regularCauchyReciprocal_decode_encode :
    ∀ h : BHist,
      regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem RegularCauchyReciprocalTasteGate_single_carrier_alignment_mk_congr
    {Q Q' A A' M M' W W' D D' B B' T T' E E' H H' C C' P P' N N' : BHist}
    (hQ : Q = Q') (hA : A = A') (hM : M = M') (hW : W = W')
    (hD : D = D') (hB : B = B') (hT : T = T') (hE : E = E')
    (hH : H = H') (hC : C = C') (hP : P = P') (hN : N = N') :
    RegularCauchyReciprocalUp.mk Q A M W D B T E H C P N =
      RegularCauchyReciprocalUp.mk Q' A' M' W' D' B' T' E' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hA
  cases hM
  cases hW
  cases hD
  cases hB
  cases hT
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyReciprocalFields :
    RegularCauchyReciprocalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyReciprocalUp.mk Q A M W D B T E H C P N =>
      [Q, A, M, W, D, B, T, E, H, C, P, N]

def regularCauchyReciprocalToEventFlow :
    RegularCauchyReciprocalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyReciprocalFields x).map regularCauchyReciprocalEncodeBHist

def regularCauchyReciprocalFromEventFlow :
    EventFlow → Option RegularCauchyReciprocalUp
  -- BEDC touchpoint anchor: BHist BMark
  | Q :: restQ =>
      match restQ with
      | A :: restA =>
          match restA with
          | M :: restM =>
              match restM with
              | W :: restW =>
                  match restW with
                  | D :: restD =>
                      match restD with
                      | B :: restB =>
                          match restB with
                          | T :: restT =>
                              match restT with
                              | E :: restE =>
                                  match restE with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (RegularCauchyReciprocalUp.mk
                                                          (regularCauchyReciprocalDecodeBHist Q)
                                                          (regularCauchyReciprocalDecodeBHist A)
                                                          (regularCauchyReciprocalDecodeBHist M)
                                                          (regularCauchyReciprocalDecodeBHist W)
                                                          (regularCauchyReciprocalDecodeBHist D)
                                                          (regularCauchyReciprocalDecodeBHist B)
                                                          (regularCauchyReciprocalDecodeBHist T)
                                                          (regularCauchyReciprocalDecodeBHist E)
                                                          (regularCauchyReciprocalDecodeBHist H)
                                                          (regularCauchyReciprocalDecodeBHist C)
                                                          (regularCauchyReciprocalDecodeBHist P)
                                                          (regularCauchyReciprocalDecodeBHist N))
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

private theorem regularCauchyReciprocal_round_trip :
    ∀ x : RegularCauchyReciprocalUp,
      regularCauchyReciprocalFromEventFlow (regularCauchyReciprocalToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q A M W D B T E H C P N =>
      change
        some
            (RegularCauchyReciprocalUp.mk
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist Q))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist A))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist M))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist W))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist D))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist B))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist T))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist E))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist H))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist C))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist P))
              (regularCauchyReciprocalDecodeBHist
                (regularCauchyReciprocalEncodeBHist N))) =
          some (RegularCauchyReciprocalUp.mk Q A M W D B T E H C P N)
      exact
        congrArg some
          (RegularCauchyReciprocalTasteGate_single_carrier_alignment_mk_congr
            (regularCauchyReciprocal_decode_encode Q)
            (regularCauchyReciprocal_decode_encode A)
            (regularCauchyReciprocal_decode_encode M)
            (regularCauchyReciprocal_decode_encode W)
            (regularCauchyReciprocal_decode_encode D)
            (regularCauchyReciprocal_decode_encode B)
            (regularCauchyReciprocal_decode_encode T)
            (regularCauchyReciprocal_decode_encode E)
            (regularCauchyReciprocal_decode_encode H)
            (regularCauchyReciprocal_decode_encode C)
            (regularCauchyReciprocal_decode_encode P)
            (regularCauchyReciprocal_decode_encode N))

private theorem regularCauchyReciprocalToEventFlow_injective
    {x y : RegularCauchyReciprocalUp} :
    regularCauchyReciprocalToEventFlow x =
        regularCauchyReciprocalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchyReciprocalFromEventFlow
            (regularCauchyReciprocalToEventFlow x) :=
        (regularCauchyReciprocal_round_trip x).symm
      _ =
          regularCauchyReciprocalFromEventFlow
            (regularCauchyReciprocalToEventFlow y) :=
        congrArg regularCauchyReciprocalFromEventFlow hxy
      _ = some y := regularCauchyReciprocal_round_trip y
  exact Option.some.inj optionEq

instance regularCauchyReciprocalBHistCarrier :
    BHistCarrier RegularCauchyReciprocalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyReciprocalToEventFlow
  fromEventFlow := regularCauchyReciprocalFromEventFlow

instance regularCauchyReciprocalChapterTasteGate :
    ChapterTasteGate RegularCauchyReciprocalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyReciprocalFromEventFlow (regularCauchyReciprocalToEventFlow x) =
        some x
    exact regularCauchyReciprocal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyReciprocalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyReciprocalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyReciprocalChapterTasteGate

theorem RegularCauchyReciprocalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyReciprocalUp,
        regularCauchyReciprocalFromEventFlow
            (regularCauchyReciprocalToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyReciprocalUp,
        regularCauchyReciprocalToEventFlow x =
            regularCauchyReciprocalToEventFlow y →
          x = y) ∧
      regularCauchyReciprocalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyReciprocal_decode_encode,
      regularCauchyReciprocal_round_trip,
      (fun _ _ heq => regularCauchyReciprocalToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyReciprocalUp
