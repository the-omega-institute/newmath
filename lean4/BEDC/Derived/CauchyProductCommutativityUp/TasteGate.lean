import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductCommutativityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductCommutativityUp : Type where
  | mk (Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N : BHist) :
      CauchyProductCommutativityUp
  deriving DecidableEq

def cauchyProductCommutativityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductCommutativityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductCommutativityEncodeBHist h

def cauchyProductCommutativityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductCommutativityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductCommutativityDecodeBHist tail)

private theorem cauchyProductCommutativity_decode_encode_bhist :
    ∀ h : BHist,
      cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyProductCommutativityEncodeBHist_injective {h k : BHist} :
    cauchyProductCommutativityEncodeBHist h =
      cauchyProductCommutativityEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductCommutativityDecodeBHist
          (cauchyProductCommutativityEncodeBHist h) =
        cauchyProductCommutativityDecodeBHist
          (cauchyProductCommutativityEncodeBHist k) :=
    congrArg cauchyProductCommutativityDecodeBHist heq
  exact
    Eq.trans (cauchyProductCommutativity_decode_encode_bhist h).symm
      (Eq.trans hread (cauchyProductCommutativity_decode_encode_bhist k))

private theorem cauchyProductCommutativity_mk_congr
    {Pxy Pxy' Pyx Pyx' Wx Wx' Wy Wy' Dxy Dxy' Dyx Dyx' Rxy Rxy' Ryx Ryx'
      Exy Exy' Eyx Eyx' H H' C C' Q Q' N N' : BHist}
    (hPxy : Pxy' = Pxy) (hPyx : Pyx' = Pyx) (hWx : Wx' = Wx) (hWy : Wy' = Wy)
    (hDxy : Dxy' = Dxy) (hDyx : Dyx' = Dyx) (hRxy : Rxy' = Rxy)
    (hRyx : Ryx' = Ryx) (hExy : Exy' = Exy) (hEyx : Eyx' = Eyx)
    (hH : H' = H) (hC : C' = C) (hQ : Q' = Q) (hN : N' = N) :
    CauchyProductCommutativityUp.mk Pxy' Pyx' Wx' Wy' Dxy' Dyx' Rxy' Ryx'
        Exy' Eyx' H' C' Q' N' =
      CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q
        N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hPxy
  cases hPyx
  cases hWx
  cases hWy
  cases hDxy
  cases hDyx
  cases hRxy
  cases hRyx
  cases hExy
  cases hEyx
  cases hH
  cases hC
  cases hQ
  cases hN
  rfl

def cauchyProductCommutativityFields :
    CauchyProductCommutativityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N =>
      [Pxy, Pyx, Wx, Wy, Dxy, Dyx, Rxy, Ryx, Exy, Eyx, H, C, Q, N]

def cauchyProductCommutativityToEventFlow :
    CauchyProductCommutativityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyProductCommutativityFields x).map
      cauchyProductCommutativityEncodeBHist

def cauchyProductCommutativityFromEventFlow :
    EventFlow → Option CauchyProductCommutativityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Pxy :: rest0 =>
      match rest0 with
      | [] => none
      | Pyx :: rest1 =>
          match rest1 with
          | [] => none
          | Wx :: rest2 =>
              match rest2 with
              | [] => none
              | Wy :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Dxy :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Dyx :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Rxy :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Ryx :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | Exy :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | Eyx :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | H :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | Q :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | N :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (CauchyProductCommutativityUp.mk
                                                                  (cauchyProductCommutativityDecodeBHist Pxy)
                                                                  (cauchyProductCommutativityDecodeBHist Pyx)
                                                                  (cauchyProductCommutativityDecodeBHist Wx)
                                                                  (cauchyProductCommutativityDecodeBHist Wy)
                                                                  (cauchyProductCommutativityDecodeBHist Dxy)
                                                                  (cauchyProductCommutativityDecodeBHist Dyx)
                                                                  (cauchyProductCommutativityDecodeBHist Rxy)
                                                                  (cauchyProductCommutativityDecodeBHist Ryx)
                                                                  (cauchyProductCommutativityDecodeBHist Exy)
                                                                  (cauchyProductCommutativityDecodeBHist Eyx)
                                                                  (cauchyProductCommutativityDecodeBHist H)
                                                                  (cauchyProductCommutativityDecodeBHist C)
                                                                  (cauchyProductCommutativityDecodeBHist Q)
                                                                  (cauchyProductCommutativityDecodeBHist N))
                                                          | _ :: _ => none

private theorem cauchyProductCommutativity_round_trip :
    ∀ x : CauchyProductCommutativityUp,
      cauchyProductCommutativityFromEventFlow
        (cauchyProductCommutativityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N =>
      exact
        congrArg some
          (cauchyProductCommutativity_mk_congr
            (cauchyProductCommutativity_decode_encode_bhist Pxy)
            (cauchyProductCommutativity_decode_encode_bhist Pyx)
            (cauchyProductCommutativity_decode_encode_bhist Wx)
            (cauchyProductCommutativity_decode_encode_bhist Wy)
            (cauchyProductCommutativity_decode_encode_bhist Dxy)
            (cauchyProductCommutativity_decode_encode_bhist Dyx)
            (cauchyProductCommutativity_decode_encode_bhist Rxy)
            (cauchyProductCommutativity_decode_encode_bhist Ryx)
            (cauchyProductCommutativity_decode_encode_bhist Exy)
            (cauchyProductCommutativity_decode_encode_bhist Eyx)
            (cauchyProductCommutativity_decode_encode_bhist H)
            (cauchyProductCommutativity_decode_encode_bhist C)
            (cauchyProductCommutativity_decode_encode_bhist Q)
            (cauchyProductCommutativity_decode_encode_bhist N))

private theorem cauchyProductCommutativityToEventFlow_injective
    {x y : CauchyProductCommutativityUp} :
    cauchyProductCommutativityToEventFlow x =
      cauchyProductCommutativityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductCommutativityFromEventFlow
          (cauchyProductCommutativityToEventFlow x) =
        cauchyProductCommutativityFromEventFlow
          (cauchyProductCommutativityToEventFlow y) :=
    congrArg cauchyProductCommutativityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyProductCommutativity_round_trip x).symm
      (Eq.trans hread (cauchyProductCommutativity_round_trip y)))

instance cauchyProductCommutativityBHistCarrier :
    BHistCarrier CauchyProductCommutativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductCommutativityToEventFlow
  fromEventFlow := cauchyProductCommutativityFromEventFlow

instance cauchyProductCommutativityChapterTasteGate :
    ChapterTasteGate CauchyProductCommutativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyProductCommutativityFromEventFlow
        (cauchyProductCommutativityToEventFlow x) = some x
    exact cauchyProductCommutativity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyProductCommutativityToEventFlow_injective heq)

instance cauchyProductCommutativityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyProductCommutativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyProductCommutativityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyProductCommutativityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyProductCommutativityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyProductCommutativityChapterTasteGate

theorem CauchyProductCommutativityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEncodeBHist h) = h) ∧
      (∀ x : CauchyProductCommutativityUp,
        cauchyProductCommutativityFromEventFlow
          (cauchyProductCommutativityToEventFlow x) = some x) ∧
        (∀ x y : CauchyProductCommutativityUp,
          cauchyProductCommutativityToEventFlow x =
            cauchyProductCommutativityToEventFlow y → x = y) ∧
          cauchyProductCommutativityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyProductCommutativity_decode_encode_bhist
  · constructor
    · exact cauchyProductCommutativity_round_trip
    · constructor
      · intro x y heq
        cases x with
        | mk Pxy1 Pyx1 Wx1 Wy1 Dxy1 Dyx1 Rxy1 Ryx1 Exy1 Eyx1 H1 C1 Q1 N1 =>
            cases y with
            | mk Pxy2 Pyx2 Wx2 Wy2 Dxy2 Dyx2 Rxy2 Ryx2 Exy2 Eyx2 H2 C2 Q2 N2 =>
                change
                  [cauchyProductCommutativityEncodeBHist Pxy1,
                      cauchyProductCommutativityEncodeBHist Pyx1,
                      cauchyProductCommutativityEncodeBHist Wx1,
                      cauchyProductCommutativityEncodeBHist Wy1,
                      cauchyProductCommutativityEncodeBHist Dxy1,
                      cauchyProductCommutativityEncodeBHist Dyx1,
                      cauchyProductCommutativityEncodeBHist Rxy1,
                      cauchyProductCommutativityEncodeBHist Ryx1,
                      cauchyProductCommutativityEncodeBHist Exy1,
                      cauchyProductCommutativityEncodeBHist Eyx1,
                      cauchyProductCommutativityEncodeBHist H1,
                      cauchyProductCommutativityEncodeBHist C1,
                      cauchyProductCommutativityEncodeBHist Q1,
                      cauchyProductCommutativityEncodeBHist N1] =
                    [cauchyProductCommutativityEncodeBHist Pxy2,
                      cauchyProductCommutativityEncodeBHist Pyx2,
                      cauchyProductCommutativityEncodeBHist Wx2,
                      cauchyProductCommutativityEncodeBHist Wy2,
                      cauchyProductCommutativityEncodeBHist Dxy2,
                      cauchyProductCommutativityEncodeBHist Dyx2,
                      cauchyProductCommutativityEncodeBHist Rxy2,
                      cauchyProductCommutativityEncodeBHist Ryx2,
                      cauchyProductCommutativityEncodeBHist Exy2,
                      cauchyProductCommutativityEncodeBHist Eyx2,
                      cauchyProductCommutativityEncodeBHist H2,
                      cauchyProductCommutativityEncodeBHist C2,
                      cauchyProductCommutativityEncodeBHist Q2,
                      cauchyProductCommutativityEncodeBHist N2] at heq
                injection heq with hPxy t1
                injection t1 with hPyx t2
                injection t2 with hWx t3
                injection t3 with hWy t4
                injection t4 with hDxy t5
                injection t5 with hDyx t6
                injection t6 with hRxy t7
                injection t7 with hRyx t8
                injection t8 with hExy t9
                injection t9 with hEyx t10
                injection t10 with hH t11
                injection t11 with hC t12
                injection t12 with hQ t13
                injection t13 with hN _
                exact
                  cauchyProductCommutativity_mk_congr
                    (cauchyProductCommutativityEncodeBHist_injective hPxy)
                    (cauchyProductCommutativityEncodeBHist_injective hPyx)
                    (cauchyProductCommutativityEncodeBHist_injective hWx)
                    (cauchyProductCommutativityEncodeBHist_injective hWy)
                    (cauchyProductCommutativityEncodeBHist_injective hDxy)
                    (cauchyProductCommutativityEncodeBHist_injective hDyx)
                    (cauchyProductCommutativityEncodeBHist_injective hRxy)
                    (cauchyProductCommutativityEncodeBHist_injective hRyx)
                    (cauchyProductCommutativityEncodeBHist_injective hExy)
                    (cauchyProductCommutativityEncodeBHist_injective hEyx)
                    (cauchyProductCommutativityEncodeBHist_injective hH)
                    (cauchyProductCommutativityEncodeBHist_injective hC)
                    (cauchyProductCommutativityEncodeBHist_injective hQ)
                    (cauchyProductCommutativityEncodeBHist_injective hN)
      · rfl

end BEDC.Derived.CauchyProductCommutativityUp
