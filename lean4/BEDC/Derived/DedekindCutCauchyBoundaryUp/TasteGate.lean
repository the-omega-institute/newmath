import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindCutCauchyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindCutCauchyBoundaryUp : Type where
  | mk (L U K Q S R D E H C P N : BHist) : DedekindCutCauchyBoundaryUp
  deriving DecidableEq

def dedekindCutCauchyBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindCutCauchyBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindCutCauchyBoundaryEncodeBHist h

def dedekindCutCauchyBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindCutCauchyBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindCutCauchyBoundaryDecodeBHist tail)

theorem DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dedekindCutCauchyBoundaryFields : DedekindCutCauchyBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindCutCauchyBoundaryUp.mk L U K Q S R D E H C P N =>
      [L, U, K, Q, S, R, D, E, H, C, P, N]

def dedekindCutCauchyBoundaryToEventFlow : DedekindCutCauchyBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dedekindCutCauchyBoundaryFields x).map dedekindCutCauchyBoundaryEncodeBHist

def dedekindCutCauchyBoundaryFromEventFlow : EventFlow → Option DedekindCutCauchyBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _L :: [] => none
  | _L :: _U :: [] => none
  | _L :: _U :: _K :: [] => none
  | _L :: _U :: _K :: _Q :: [] => none
  | _L :: _U :: _K :: _Q :: _S :: [] => none
  | _L :: _U :: _K :: _Q :: _S :: _R :: [] => none
  | _L :: _U :: _K :: _Q :: _S :: _R :: _D :: [] => none
  | _L :: _U :: _K :: _Q :: _S :: _R :: _D :: _E :: [] => none
  | _L :: _U :: _K :: _Q :: _S :: _R :: _D :: _E :: _H :: [] => none
  | _L :: _U :: _K :: _Q :: _S :: _R :: _D :: _E :: _H :: _C :: [] => none
  | _L :: _U :: _K :: _Q :: _S :: _R :: _D :: _E :: _H :: _C :: _P :: [] => none
  | L :: U :: K :: Q :: S :: R :: D :: E :: H :: C :: P :: N :: [] =>
      some
        (DedekindCutCauchyBoundaryUp.mk
          (dedekindCutCauchyBoundaryDecodeBHist L)
          (dedekindCutCauchyBoundaryDecodeBHist U)
          (dedekindCutCauchyBoundaryDecodeBHist K)
          (dedekindCutCauchyBoundaryDecodeBHist Q)
          (dedekindCutCauchyBoundaryDecodeBHist S)
          (dedekindCutCauchyBoundaryDecodeBHist R)
          (dedekindCutCauchyBoundaryDecodeBHist D)
          (dedekindCutCauchyBoundaryDecodeBHist E)
          (dedekindCutCauchyBoundaryDecodeBHist H)
          (dedekindCutCauchyBoundaryDecodeBHist C)
          (dedekindCutCauchyBoundaryDecodeBHist P)
          (dedekindCutCauchyBoundaryDecodeBHist N))
  | _L :: _U :: _K :: _Q :: _S :: _R :: _D :: _E :: _H :: _C :: _P :: _N ::
      _extra :: _rest => none

private theorem dedekindCutCauchyBoundary_mk_congr
    {L L' U U' K K' Q Q' S S' R R' D D' E E' H H' C C' P P' N N' : BHist}
    (hL : L' = L) (hU : U' = U) (hK : K' = K) (hQ : Q' = Q)
    (hS : S' = S) (hR : R' = R) (hD : D' = D) (hE : E' = E)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    DedekindCutCauchyBoundaryUp.mk L' U' K' Q' S' R' D' E' H' C' P' N' =
      DedekindCutCauchyBoundaryUp.mk L U K Q S R D E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL
  cases hU
  cases hK
  cases hQ
  cases hS
  cases hR
  cases hD
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

theorem DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DedekindCutCauchyBoundaryUp,
      dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U K Q S R D E H C P N =>
      exact
        congrArg some
          (dedekindCutCauchyBoundary_mk_congr
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode L)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode U)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode K)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode Q)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode S)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode R)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode D)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode E)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode H)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode C)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode P)
            (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode N))

theorem DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DedekindCutCauchyBoundaryUp} :
    dedekindCutCauchyBoundaryToEventFlow x =
      dedekindCutCauchyBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindCutCauchyBoundaryFromEventFlow (dedekindCutCauchyBoundaryToEventFlow x) =
        dedekindCutCauchyBoundaryFromEventFlow (dedekindCutCauchyBoundaryToEventFlow y) :=
    congrArg dedekindCutCauchyBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance dedekindCutCauchyBoundaryBHistCarrier :
    BHistCarrier DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindCutCauchyBoundaryToEventFlow
  fromEventFlow := dedekindCutCauchyBoundaryFromEventFlow

instance dedekindCutCauchyBoundaryChapterTasteGate :
    ChapterTasteGate DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow x) =
        some x
    exact DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DedekindCutCauchyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindCutCauchyBoundaryChapterTasteGate

theorem DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEncodeBHist h) = h) ∧
      (∀ x : DedekindCutCauchyBoundaryUp,
        dedekindCutCauchyBoundaryFromEventFlow
            (dedekindCutCauchyBoundaryToEventFlow x) =
          some x) ∧
      (∀ x y : DedekindCutCauchyBoundaryUp,
        dedekindCutCauchyBoundaryToEventFlow x =
          dedekindCutCauchyBoundaryToEventFlow y → x = y) ∧
      dedekindCutCauchyBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.DedekindCutCauchyBoundaryUp
