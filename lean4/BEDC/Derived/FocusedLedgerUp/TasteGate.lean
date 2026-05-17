import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FocusedLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FocusedLedgerUp : Type where
  | mk : (I H T F S D G R J Q rho A C P N : BHist) → FocusedLedgerUp

def focusedLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: focusedLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: focusedLedgerEncodeBHist h

def focusedLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (focusedLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (focusedLedgerDecodeBHist tail)

private theorem focusedLedgerDecode_encode_bhist :
    ∀ h : BHist, focusedLedgerDecodeBHist (focusedLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem focusedLedger_mk_congr
    {I I' H H' T T' F F' S S' D D' G G' R R' J J' Q Q' rho rho' A A' C C'
      P P' N N' : BHist}
    (hI : I' = I) (hH : H' = H) (hT : T' = T) (hF : F' = F)
    (hS : S' = S) (hD : D' = D) (hG : G' = G) (hR : R' = R)
    (hJ : J' = J) (hQ : Q' = Q) (hrho : rho' = rho) (hA : A' = A)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    FocusedLedgerUp.mk I' H' T' F' S' D' G' R' J' Q' rho' A' C' P' N' =
      FocusedLedgerUp.mk I H T F S D G R J Q rho A C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hH
  cases hT
  cases hF
  cases hS
  cases hD
  cases hG
  cases hR
  cases hJ
  cases hQ
  cases hrho
  cases hA
  cases hC
  cases hP
  cases hN
  rfl

def focusedLedgerFields : FocusedLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FocusedLedgerUp.mk I H T F S D G R J Q rho A C P N =>
      [I, H, T, F, S, D, G, R, J, Q, rho, A, C, P, N]

def focusedLedgerToEventFlow : FocusedLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (focusedLedgerFields x).map focusedLedgerEncodeBHist

def focusedLedgerFromEventFlow : EventFlow → Option FocusedLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _I :: [] => none
  | _I :: _H :: [] => none
  | _I :: _H :: _T :: [] => none
  | _I :: _H :: _T :: _F :: [] => none
  | _I :: _H :: _T :: _F :: _S :: [] => none
  | _I :: _H :: _T :: _F :: _S :: _D :: [] => none
  | _I :: _H :: _T :: _F :: _S :: _D :: _G :: [] => none
  | _I :: _H :: _T :: _F :: _S :: _D :: _G :: _R :: [] => none
  | _I :: _H :: _T :: _F :: _S :: _D :: _G :: _R :: _J :: [] => none
  | _I :: _H :: _T :: _F :: _S :: _D :: _G :: _R :: _J :: _Q :: [] => none
  | _I :: _H :: _T :: _F :: _S :: _D :: _G :: _R :: _J :: _Q :: _rho :: [] =>
      none
  | _I :: _H :: _T :: _F :: _S :: _D :: _G :: _R :: _J :: _Q :: _rho :: _A :: [] =>
      none
  | _I :: _H :: _T :: _F :: _S :: _D :: _G :: _R :: _J :: _Q :: _rho :: _A ::
      _C :: [] =>
      none
  | _I :: _H :: _T :: _F :: _S :: _D :: _G :: _R :: _J :: _Q :: _rho :: _A ::
      _C :: _P :: [] =>
      none
  | I :: H :: T :: F :: S :: D :: G :: R :: J :: Q :: rho :: A :: C :: P :: N :: [] =>
      some
        (FocusedLedgerUp.mk
          (focusedLedgerDecodeBHist I)
          (focusedLedgerDecodeBHist H)
          (focusedLedgerDecodeBHist T)
          (focusedLedgerDecodeBHist F)
          (focusedLedgerDecodeBHist S)
          (focusedLedgerDecodeBHist D)
          (focusedLedgerDecodeBHist G)
          (focusedLedgerDecodeBHist R)
          (focusedLedgerDecodeBHist J)
          (focusedLedgerDecodeBHist Q)
          (focusedLedgerDecodeBHist rho)
          (focusedLedgerDecodeBHist A)
          (focusedLedgerDecodeBHist C)
          (focusedLedgerDecodeBHist P)
          (focusedLedgerDecodeBHist N))
  | _I :: _H :: _T :: _F :: _S :: _D :: _G :: _R :: _J :: _Q :: _rho :: _A ::
      _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem focusedLedger_round_trip :
    ∀ x : FocusedLedgerUp,
      focusedLedgerFromEventFlow (focusedLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I H T F S D G R J Q rho A C P N =>
      exact
        congrArg some
          (focusedLedger_mk_congr
            (focusedLedgerDecode_encode_bhist I)
            (focusedLedgerDecode_encode_bhist H)
            (focusedLedgerDecode_encode_bhist T)
            (focusedLedgerDecode_encode_bhist F)
            (focusedLedgerDecode_encode_bhist S)
            (focusedLedgerDecode_encode_bhist D)
            (focusedLedgerDecode_encode_bhist G)
            (focusedLedgerDecode_encode_bhist R)
            (focusedLedgerDecode_encode_bhist J)
            (focusedLedgerDecode_encode_bhist Q)
            (focusedLedgerDecode_encode_bhist rho)
            (focusedLedgerDecode_encode_bhist A)
            (focusedLedgerDecode_encode_bhist C)
            (focusedLedgerDecode_encode_bhist P)
            (focusedLedgerDecode_encode_bhist N))

private theorem focusedLedgerToEventFlow_injective {x y : FocusedLedgerUp} :
    focusedLedgerToEventFlow x = focusedLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      focusedLedgerFromEventFlow (focusedLedgerToEventFlow x) =
        focusedLedgerFromEventFlow (focusedLedgerToEventFlow y) :=
    congrArg focusedLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (focusedLedger_round_trip x).symm
      (Eq.trans hread (focusedLedger_round_trip y)))

private theorem focusedLedger_field_faithful :
    ∀ x y : FocusedLedgerUp, focusedLedgerFields x = focusedLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I H T F S D G R J Q rho A C P N =>
      cases y with
      | mk I' H' T' F' S' D' G' R' J' Q' rho' A' C' P' N' =>
          cases hfields
          rfl

instance focusedLedgerBHistCarrier : BHistCarrier FocusedLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := focusedLedgerToEventFlow
  fromEventFlow := focusedLedgerFromEventFlow

instance focusedLedgerChapterTasteGate : ChapterTasteGate FocusedLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change focusedLedgerFromEventFlow (focusedLedgerToEventFlow x) = some x
    exact focusedLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (focusedLedgerToEventFlow_injective heq)

instance focusedLedgerFieldFaithful : FieldFaithful FocusedLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := focusedLedgerFields
  field_faithful := focusedLedger_field_faithful

instance focusedLedgerNontrivial : BEDC.Meta.TasteGate.Nontrivial FocusedLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FocusedLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      FocusedLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FocusedLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  focusedLedgerChapterTasteGate

theorem FocusedLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, focusedLedgerDecodeBHist (focusedLedgerEncodeBHist h) = h) ∧
      (∀ x : FocusedLedgerUp,
        focusedLedgerFromEventFlow (focusedLedgerToEventFlow x) = some x) ∧
        (∀ x y : FocusedLedgerUp,
          focusedLedgerToEventFlow x = focusedLedgerToEventFlow y → x = y) ∧
          focusedLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact focusedLedgerDecode_encode_bhist
  · constructor
    · exact focusedLedger_round_trip
    · constructor
      · intro x y heq
        exact focusedLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.FocusedLedgerUp
