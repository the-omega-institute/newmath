import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyApproximationSchemeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyApproximationSchemeUp : Type where
  | mk (D S M R W Q H C P N : BHist) : CauchyApproximationSchemeUp
  deriving DecidableEq

def cauchyApproximationSchemeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyApproximationSchemeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyApproximationSchemeEncodeBHist h

def cauchyApproximationSchemeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyApproximationSchemeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyApproximationSchemeDecodeBHist tail)

private theorem cauchyApproximationSchemeDecode_encode_bhist :
    ∀ h : BHist,
      cauchyApproximationSchemeDecodeBHist
        (cauchyApproximationSchemeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyApproximationScheme_mk_congr
    {D D' S S' M M' R R' W W' Q Q' H H' C C' P P' N N' : BHist}
    (hD : D' = D) (hS : S' = S) (hM : M' = M) (hR : R' = R) (hW : W' = W)
    (hQ : Q' = Q) (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyApproximationSchemeUp.mk D' S' M' R' W' Q' H' C' P' N' =
      CauchyApproximationSchemeUp.mk D S M R W Q H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hS
  cases hM
  cases hR
  cases hW
  cases hQ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyApproximationSchemeFields :
    CauchyApproximationSchemeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyApproximationSchemeUp.mk D S M R W Q H C P N => [D, S, M, R, W, Q, H, C, P, N]

def cauchyApproximationSchemeToEventFlow :
    CauchyApproximationSchemeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyApproximationSchemeFields x).map cauchyApproximationSchemeEncodeBHist

def cauchyApproximationSchemeFromEventFlow :
    EventFlow → Option CauchyApproximationSchemeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _D :: [] => none
  | _D :: _S :: [] => none
  | _D :: _S :: _M :: [] => none
  | _D :: _S :: _M :: _R :: [] => none
  | _D :: _S :: _M :: _R :: _W :: [] => none
  | _D :: _S :: _M :: _R :: _W :: _Q :: [] => none
  | _D :: _S :: _M :: _R :: _W :: _Q :: _H :: [] => none
  | _D :: _S :: _M :: _R :: _W :: _Q :: _H :: _C :: [] => none
  | _D :: _S :: _M :: _R :: _W :: _Q :: _H :: _C :: _P :: [] => none
  | D :: S :: M :: R :: W :: Q :: H :: C :: P :: N :: [] =>
      some
        (CauchyApproximationSchemeUp.mk
          (cauchyApproximationSchemeDecodeBHist D)
          (cauchyApproximationSchemeDecodeBHist S)
          (cauchyApproximationSchemeDecodeBHist M)
          (cauchyApproximationSchemeDecodeBHist R)
          (cauchyApproximationSchemeDecodeBHist W)
          (cauchyApproximationSchemeDecodeBHist Q)
          (cauchyApproximationSchemeDecodeBHist H)
          (cauchyApproximationSchemeDecodeBHist C)
          (cauchyApproximationSchemeDecodeBHist P)
          (cauchyApproximationSchemeDecodeBHist N))
  | _D :: _S :: _M :: _R :: _W :: _Q :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem cauchyApproximationScheme_round_trip :
    ∀ x : CauchyApproximationSchemeUp,
      cauchyApproximationSchemeFromEventFlow
        (cauchyApproximationSchemeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S M R W Q H C P N =>
      exact
        congrArg some
          (cauchyApproximationScheme_mk_congr
            (cauchyApproximationSchemeDecode_encode_bhist D)
            (cauchyApproximationSchemeDecode_encode_bhist S)
            (cauchyApproximationSchemeDecode_encode_bhist M)
            (cauchyApproximationSchemeDecode_encode_bhist R)
            (cauchyApproximationSchemeDecode_encode_bhist W)
            (cauchyApproximationSchemeDecode_encode_bhist Q)
            (cauchyApproximationSchemeDecode_encode_bhist H)
            (cauchyApproximationSchemeDecode_encode_bhist C)
            (cauchyApproximationSchemeDecode_encode_bhist P)
            (cauchyApproximationSchemeDecode_encode_bhist N))

private theorem cauchyApproximationSchemeToEventFlow_injective
    {x y : CauchyApproximationSchemeUp} :
    cauchyApproximationSchemeToEventFlow x =
      cauchyApproximationSchemeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyApproximationSchemeFromEventFlow
          (cauchyApproximationSchemeToEventFlow x) =
        cauchyApproximationSchemeFromEventFlow
          (cauchyApproximationSchemeToEventFlow y) :=
    congrArg cauchyApproximationSchemeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyApproximationScheme_round_trip x).symm
      (Eq.trans hread (cauchyApproximationScheme_round_trip y)))

private theorem cauchyApproximationScheme_field_faithful :
    ∀ x y : CauchyApproximationSchemeUp,
      cauchyApproximationSchemeFields x =
        cauchyApproximationSchemeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D S M R W Q H C P N =>
      cases y with
      | mk D' S' M' R' W' Q' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyApproximationSchemeBHistCarrier :
    BHistCarrier CauchyApproximationSchemeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyApproximationSchemeToEventFlow
  fromEventFlow := cauchyApproximationSchemeFromEventFlow

instance cauchyApproximationSchemeChapterTasteGate :
    ChapterTasteGate CauchyApproximationSchemeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyApproximationSchemeFromEventFlow
        (cauchyApproximationSchemeToEventFlow x) = some x
    exact cauchyApproximationScheme_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyApproximationSchemeToEventFlow_injective heq)

instance cauchyApproximationSchemeFieldFaithful :
    FieldFaithful CauchyApproximationSchemeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyApproximationSchemeFields
  field_faithful := cauchyApproximationScheme_field_faithful

instance cauchyApproximationSchemeNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyApproximationSchemeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyApproximationSchemeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyApproximationSchemeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyApproximationSchemeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyApproximationSchemeChapterTasteGate

theorem CauchyApproximationSchemeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyApproximationSchemeUp) ∧
      Nonempty (FieldFaithful CauchyApproximationSchemeUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyApproximationSchemeUp) ∧
          (∀ h : BHist,
            cauchyApproximationSchemeDecodeBHist
              (cauchyApproximationSchemeEncodeBHist h) = h) ∧
            (∀ x : CauchyApproximationSchemeUp,
              cauchyApproximationSchemeFromEventFlow
                (cauchyApproximationSchemeToEventFlow x) = some x) ∧
              cauchyApproximationSchemeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨cauchyApproximationSchemeChapterTasteGate⟩,
      ⟨cauchyApproximationSchemeFieldFaithful⟩,
      ⟨cauchyApproximationSchemeNontrivial⟩,
      cauchyApproximationSchemeDecode_encode_bhist,
      cauchyApproximationScheme_round_trip,
      rfl⟩

end BEDC.Derived.CauchyApproximationSchemeUp
