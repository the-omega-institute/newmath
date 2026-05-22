import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SternBrocotUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SternBrocotUp : Type where
  | mk (A L U M F B Q R H C P N : BHist) : SternBrocotUp
  deriving DecidableEq

def sternBrocotEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sternBrocotEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sternBrocotEncodeBHist h

def sternBrocotDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sternBrocotDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sternBrocotDecodeBHist tail)

theorem SternBrocotTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, sternBrocotDecodeBHist (sternBrocotEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sternBrocotFields : SternBrocotUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SternBrocotUp.mk A L U M F B Q R H C P N => [A, L, U, M, F, B, Q, R, H, C, P, N]

def sternBrocotToEventFlow : SternBrocotUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sternBrocotFields x).map sternBrocotEncodeBHist

def sternBrocotFromEventFlow : EventFlow → Option SternBrocotUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _A :: [] => none
  | _A :: _L :: [] => none
  | _A :: _L :: _U :: [] => none
  | _A :: _L :: _U :: _M :: [] => none
  | _A :: _L :: _U :: _M :: _F :: [] => none
  | _A :: _L :: _U :: _M :: _F :: _B :: [] => none
  | _A :: _L :: _U :: _M :: _F :: _B :: _Q :: [] => none
  | _A :: _L :: _U :: _M :: _F :: _B :: _Q :: _R :: [] => none
  | _A :: _L :: _U :: _M :: _F :: _B :: _Q :: _R :: _H :: [] => none
  | _A :: _L :: _U :: _M :: _F :: _B :: _Q :: _R :: _H :: _C :: [] => none
  | _A :: _L :: _U :: _M :: _F :: _B :: _Q :: _R :: _H :: _C :: _P :: [] => none
  | A :: L :: U :: M :: F :: B :: Q :: R :: H :: C :: P :: N :: [] =>
      some
        (SternBrocotUp.mk
          (sternBrocotDecodeBHist A)
          (sternBrocotDecodeBHist L)
          (sternBrocotDecodeBHist U)
          (sternBrocotDecodeBHist M)
          (sternBrocotDecodeBHist F)
          (sternBrocotDecodeBHist B)
          (sternBrocotDecodeBHist Q)
          (sternBrocotDecodeBHist R)
          (sternBrocotDecodeBHist H)
          (sternBrocotDecodeBHist C)
          (sternBrocotDecodeBHist P)
          (sternBrocotDecodeBHist N))
  | _A :: _L :: _U :: _M :: _F :: _B :: _Q :: _R :: _H :: _C :: _P :: _N ::
      _extra :: _rest => none

private theorem sternBrocot_mk_congr
    {A A' L L' U U' M M' F F' B B' Q Q' R R' H H' C C' P P' N N' : BHist}
    (hA : A' = A) (hL : L' = L) (hU : U' = U) (hM : M' = M)
    (hF : F' = F) (hB : B' = B) (hQ : Q' = Q) (hR : R' = R)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    SternBrocotUp.mk A' L' U' M' F' B' Q' R' H' C' P' N' =
      SternBrocotUp.mk A L U M F B Q R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hL
  cases hU
  cases hM
  cases hF
  cases hB
  cases hQ
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

theorem SternBrocotTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SternBrocotUp,
      sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A L U M F B Q R H C P N =>
      exact
        congrArg some
          (sternBrocot_mk_congr
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode A)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode L)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode U)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode M)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode F)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode B)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode Q)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode R)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode H)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode C)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode P)
            (SternBrocotTasteGate_single_carrier_alignment_decode_encode N))

theorem SternBrocotTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SternBrocotUp} :
    sternBrocotToEventFlow x = sternBrocotToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sternBrocotFromEventFlow (sternBrocotToEventFlow x) =
        sternBrocotFromEventFlow (sternBrocotToEventFlow y) :=
    congrArg sternBrocotFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SternBrocotTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SternBrocotTasteGate_single_carrier_alignment_round_trip y)))

instance sternBrocotBHistCarrier : BHistCarrier SternBrocotUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sternBrocotToEventFlow
  fromEventFlow := sternBrocotFromEventFlow

instance sternBrocotChapterTasteGate : ChapterTasteGate SternBrocotUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x
    exact SternBrocotTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SternBrocotTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SternBrocotUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sternBrocotChapterTasteGate

theorem SternBrocotTasteGate_single_carrier_alignment :
    (∀ h : BHist, sternBrocotDecodeBHist (sternBrocotEncodeBHist h) = h) ∧
      (∀ x : SternBrocotUp,
        sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x) ∧
      (∀ x y : SternBrocotUp,
        sternBrocotToEventFlow x = sternBrocotToEventFlow y → x = y) ∧
      sternBrocotEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SternBrocotTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact SternBrocotTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact SternBrocotTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.SternBrocotUp
