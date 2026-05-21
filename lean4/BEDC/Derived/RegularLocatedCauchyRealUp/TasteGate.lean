import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularLocatedCauchyRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularLocatedCauchyRealUp : Type where
  | mk (S Q D M L E H C P N : BHist) : RegularLocatedCauchyRealUp
  deriving DecidableEq

def regularLocatedCauchyRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularLocatedCauchyRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularLocatedCauchyRealEncodeBHist h

def regularLocatedCauchyRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularLocatedCauchyRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularLocatedCauchyRealDecodeBHist tail)

private theorem regularLocatedCauchyReal_decode_encode :
    ∀ h : BHist,
      regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem RegularLocatedCauchyRealTasteGate_single_carrier_alignment_mk_congr
    {S S' Q Q' D D' M M' L L' E E' H H' C C' P P' N N' : BHist}
    (hS : S = S') (hQ : Q = Q') (hD : D = D') (hM : M = M')
    (hL : L = L') (hE : E = E') (hH : H = H') (hC : C = C')
    (hP : P = P') (hN : N = N') :
    RegularLocatedCauchyRealUp.mk S Q D M L E H C P N =
      RegularLocatedCauchyRealUp.mk S' Q' D' M' L' E' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hQ
  cases hD
  cases hM
  cases hL
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularLocatedCauchyRealFields :
    RegularLocatedCauchyRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularLocatedCauchyRealUp.mk S Q D M L E H C P N =>
      [S, Q, D, M, L, E, H, C, P, N]

def regularLocatedCauchyRealToEventFlow :
    RegularLocatedCauchyRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularLocatedCauchyRealFields x).map regularLocatedCauchyRealEncodeBHist

def regularLocatedCauchyRealFromEventFlow :
    EventFlow → Option RegularLocatedCauchyRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | Q :: restQ =>
          match restQ with
          | D :: restD =>
              match restD with
              | M :: restM =>
                  match restM with
                  | L :: restL =>
                      match restL with
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
                                                (RegularLocatedCauchyRealUp.mk
                                                  (regularLocatedCauchyRealDecodeBHist S)
                                                  (regularLocatedCauchyRealDecodeBHist Q)
                                                  (regularLocatedCauchyRealDecodeBHist D)
                                                  (regularLocatedCauchyRealDecodeBHist M)
                                                  (regularLocatedCauchyRealDecodeBHist L)
                                                  (regularLocatedCauchyRealDecodeBHist E)
                                                  (regularLocatedCauchyRealDecodeBHist H)
                                                  (regularLocatedCauchyRealDecodeBHist C)
                                                  (regularLocatedCauchyRealDecodeBHist P)
                                                  (regularLocatedCauchyRealDecodeBHist N))
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

private theorem regularLocatedCauchyReal_round_trip :
    ∀ x : RegularLocatedCauchyRealUp,
      regularLocatedCauchyRealFromEventFlow (regularLocatedCauchyRealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q D M L E H C P N =>
      change
        some
            (RegularLocatedCauchyRealUp.mk
              (regularLocatedCauchyRealDecodeBHist
                (regularLocatedCauchyRealEncodeBHist S))
              (regularLocatedCauchyRealDecodeBHist
                (regularLocatedCauchyRealEncodeBHist Q))
              (regularLocatedCauchyRealDecodeBHist
                (regularLocatedCauchyRealEncodeBHist D))
              (regularLocatedCauchyRealDecodeBHist
                (regularLocatedCauchyRealEncodeBHist M))
              (regularLocatedCauchyRealDecodeBHist
                (regularLocatedCauchyRealEncodeBHist L))
              (regularLocatedCauchyRealDecodeBHist
                (regularLocatedCauchyRealEncodeBHist E))
              (regularLocatedCauchyRealDecodeBHist
                (regularLocatedCauchyRealEncodeBHist H))
              (regularLocatedCauchyRealDecodeBHist
                (regularLocatedCauchyRealEncodeBHist C))
              (regularLocatedCauchyRealDecodeBHist
                (regularLocatedCauchyRealEncodeBHist P))
              (regularLocatedCauchyRealDecodeBHist
                (regularLocatedCauchyRealEncodeBHist N))) =
          some (RegularLocatedCauchyRealUp.mk S Q D M L E H C P N)
      exact
        congrArg some
          (RegularLocatedCauchyRealTasteGate_single_carrier_alignment_mk_congr
            (regularLocatedCauchyReal_decode_encode S)
            (regularLocatedCauchyReal_decode_encode Q)
            (regularLocatedCauchyReal_decode_encode D)
            (regularLocatedCauchyReal_decode_encode M)
            (regularLocatedCauchyReal_decode_encode L)
            (regularLocatedCauchyReal_decode_encode E)
            (regularLocatedCauchyReal_decode_encode H)
            (regularLocatedCauchyReal_decode_encode C)
            (regularLocatedCauchyReal_decode_encode P)
            (regularLocatedCauchyReal_decode_encode N))

private theorem regularLocatedCauchyRealToEventFlow_injective
    {x y : RegularLocatedCauchyRealUp} :
    regularLocatedCauchyRealToEventFlow x =
        regularLocatedCauchyRealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularLocatedCauchyRealFromEventFlow
            (regularLocatedCauchyRealToEventFlow x) :=
        (regularLocatedCauchyReal_round_trip x).symm
      _ =
          regularLocatedCauchyRealFromEventFlow
            (regularLocatedCauchyRealToEventFlow y) :=
        congrArg regularLocatedCauchyRealFromEventFlow hxy
      _ = some y := regularLocatedCauchyReal_round_trip y
  exact Option.some.inj optionEq

instance regularLocatedCauchyRealBHistCarrier :
    BHistCarrier RegularLocatedCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularLocatedCauchyRealToEventFlow
  fromEventFlow := regularLocatedCauchyRealFromEventFlow

instance regularLocatedCauchyRealChapterTasteGate :
    ChapterTasteGate RegularLocatedCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularLocatedCauchyRealFromEventFlow (regularLocatedCauchyRealToEventFlow x) =
        some x
    exact regularLocatedCauchyReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularLocatedCauchyRealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularLocatedCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularLocatedCauchyRealChapterTasteGate

theorem RegularLocatedCauchyRealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealEncodeBHist h) =
        h) ∧
      (∀ x : RegularLocatedCauchyRealUp,
        regularLocatedCauchyRealFromEventFlow
            (regularLocatedCauchyRealToEventFlow x) =
          some x) ∧
      (∀ x y : RegularLocatedCauchyRealUp,
        regularLocatedCauchyRealToEventFlow x =
            regularLocatedCauchyRealToEventFlow y →
          x = y) ∧
      regularLocatedCauchyRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularLocatedCauchyReal_decode_encode,
      regularLocatedCauchyReal_round_trip,
      (fun _ _ heq => regularLocatedCauchyRealToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularLocatedCauchyRealUp
