import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyReindexInvarianceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyReindexInvarianceUp : Type where
  | mk (Q I T S D R E H C P N : BHist) : RegularCauchyReindexInvarianceUp

def regularCauchyReindexInvarianceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyReindexInvarianceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyReindexInvarianceEncodeBHist h

def regularCauchyReindexInvarianceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyReindexInvarianceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyReindexInvarianceDecodeBHist tail)

private theorem RegularCauchyReindexInvarianceTasteGate_decode_encode :
    ∀ h : BHist,
      regularCauchyReindexInvarianceDecodeBHist
        (regularCauchyReindexInvarianceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem regularCauchyReindexInvariance_mk_congr
    {Q Q' I I' T T' S S' D D' R R' E E' H H' C C' P P' N N' : BHist}
    (hQ : Q' = Q) (hI : I' = I) (hT : T' = T) (hS : S' = S)
    (hD : D' = D) (hR : R' = R) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RegularCauchyReindexInvarianceUp.mk Q' I' T' S' D' R' E' H' C' P' N' =
      RegularCauchyReindexInvarianceUp.mk Q I T S D R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hI
  cases hT
  cases hS
  cases hD
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyReindexInvarianceFields :
    RegularCauchyReindexInvarianceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyReindexInvarianceUp.mk Q I T S D R E H C P N =>
      [Q, I, T, S, D, R, E, H, C, P, N]

def regularCauchyReindexInvarianceToEventFlow :
    RegularCauchyReindexInvarianceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchyReindexInvarianceEncodeBHist
        (regularCauchyReindexInvarianceFields x)

def regularCauchyReindexInvarianceFromEventFlow :
    EventFlow → Option RegularCauchyReindexInvarianceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _Q :: [] => none
  | _Q :: _I :: [] => none
  | _Q :: _I :: _T :: [] => none
  | _Q :: _I :: _T :: _S :: [] => none
  | _Q :: _I :: _T :: _S :: _D :: [] => none
  | _Q :: _I :: _T :: _S :: _D :: _R :: [] => none
  | _Q :: _I :: _T :: _S :: _D :: _R :: _E :: [] => none
  | _Q :: _I :: _T :: _S :: _D :: _R :: _E :: _H :: [] => none
  | _Q :: _I :: _T :: _S :: _D :: _R :: _E :: _H :: _C :: [] => none
  | _Q :: _I :: _T :: _S :: _D :: _R :: _E :: _H :: _C :: _P :: [] => none
  | Q :: I :: T :: S :: D :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchyReindexInvarianceUp.mk
          (regularCauchyReindexInvarianceDecodeBHist Q)
          (regularCauchyReindexInvarianceDecodeBHist I)
          (regularCauchyReindexInvarianceDecodeBHist T)
          (regularCauchyReindexInvarianceDecodeBHist S)
          (regularCauchyReindexInvarianceDecodeBHist D)
          (regularCauchyReindexInvarianceDecodeBHist R)
          (regularCauchyReindexInvarianceDecodeBHist E)
          (regularCauchyReindexInvarianceDecodeBHist H)
          (regularCauchyReindexInvarianceDecodeBHist C)
          (regularCauchyReindexInvarianceDecodeBHist P)
          (regularCauchyReindexInvarianceDecodeBHist N))
  | _Q :: _I :: _T :: _S :: _D :: _R :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem RegularCauchyReindexInvarianceTasteGate_round_trip :
    ∀ x : RegularCauchyReindexInvarianceUp,
      regularCauchyReindexInvarianceFromEventFlow
        (regularCauchyReindexInvarianceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q I T S D R E H C P N =>
      exact
        congrArg some
          (regularCauchyReindexInvariance_mk_congr
            (RegularCauchyReindexInvarianceTasteGate_decode_encode Q)
            (RegularCauchyReindexInvarianceTasteGate_decode_encode I)
            (RegularCauchyReindexInvarianceTasteGate_decode_encode T)
            (RegularCauchyReindexInvarianceTasteGate_decode_encode S)
            (RegularCauchyReindexInvarianceTasteGate_decode_encode D)
            (RegularCauchyReindexInvarianceTasteGate_decode_encode R)
            (RegularCauchyReindexInvarianceTasteGate_decode_encode E)
            (RegularCauchyReindexInvarianceTasteGate_decode_encode H)
            (RegularCauchyReindexInvarianceTasteGate_decode_encode C)
            (RegularCauchyReindexInvarianceTasteGate_decode_encode P)
            (RegularCauchyReindexInvarianceTasteGate_decode_encode N))

private theorem regularCauchyReindexInvarianceToEventFlow_injective
    {x y : RegularCauchyReindexInvarianceUp} :
    regularCauchyReindexInvarianceToEventFlow x =
        regularCauchyReindexInvarianceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyReindexInvarianceFromEventFlow
          (regularCauchyReindexInvarianceToEventFlow x) =
        regularCauchyReindexInvarianceFromEventFlow
          (regularCauchyReindexInvarianceToEventFlow y) :=
    congrArg regularCauchyReindexInvarianceFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans
      (RegularCauchyReindexInvarianceTasteGate_round_trip x).symm
      (Eq.trans hread (RegularCauchyReindexInvarianceTasteGate_round_trip y))
  cases hsome
  rfl

instance regularCauchyReindexInvarianceBHistCarrier :
    BHistCarrier RegularCauchyReindexInvarianceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyReindexInvarianceToEventFlow
  fromEventFlow := regularCauchyReindexInvarianceFromEventFlow

instance regularCauchyReindexInvarianceChapterTasteGate :
    ChapterTasteGate RegularCauchyReindexInvarianceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyReindexInvarianceFromEventFlow
          (regularCauchyReindexInvarianceToEventFlow x) =
        some x
    exact RegularCauchyReindexInvarianceTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyReindexInvarianceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyReindexInvarianceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyReindexInvarianceChapterTasteGate

theorem RegularCauchyReindexInvarianceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyReindexInvarianceDecodeBHist
        (regularCauchyReindexInvarianceEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyReindexInvarianceUp,
        regularCauchyReindexInvarianceFromEventFlow
          (regularCauchyReindexInvarianceToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyReindexInvarianceUp,
          regularCauchyReindexInvarianceToEventFlow x =
              regularCauchyReindexInvarianceToEventFlow y →
            x = y) ∧
          regularCauchyReindexInvarianceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyReindexInvarianceTasteGate_decode_encode,
      RegularCauchyReindexInvarianceTasteGate_round_trip,
      (fun _ _ heq => regularCauchyReindexInvarianceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyReindexInvarianceUp
