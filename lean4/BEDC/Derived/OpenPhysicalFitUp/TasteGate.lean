import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OpenPhysicalFitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OpenPhysicalFitUp : Type where
  | mk : (H Pi O M C F E L R N : BHist) → OpenPhysicalFitUp

def openPhysicalFitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: openPhysicalFitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: openPhysicalFitEncodeBHist h

def openPhysicalFitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (openPhysicalFitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (openPhysicalFitDecodeBHist tail)

private theorem openPhysicalFitDecode_encode_bhist :
    ∀ h : BHist, openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def openPhysicalFitToEventFlow : OpenPhysicalFitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OpenPhysicalFitUp.mk H Pi O M C F E L R N =>
      [openPhysicalFitEncodeBHist H,
        openPhysicalFitEncodeBHist Pi,
        openPhysicalFitEncodeBHist O,
        openPhysicalFitEncodeBHist M,
        openPhysicalFitEncodeBHist C,
        openPhysicalFitEncodeBHist F,
        openPhysicalFitEncodeBHist E,
        openPhysicalFitEncodeBHist L,
        openPhysicalFitEncodeBHist R,
        openPhysicalFitEncodeBHist N]

def openPhysicalFitFromEventFlow : EventFlow → Option OpenPhysicalFitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | H :: rest0 =>
      match rest0 with
      | [] => none
      | Pi :: rest1 =>
          match rest1 with
          | [] => none
          | O :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | C :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | L :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | R :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (OpenPhysicalFitUp.mk
                                                  (openPhysicalFitDecodeBHist H)
                                                  (openPhysicalFitDecodeBHist Pi)
                                                  (openPhysicalFitDecodeBHist O)
                                                  (openPhysicalFitDecodeBHist M)
                                                  (openPhysicalFitDecodeBHist C)
                                                  (openPhysicalFitDecodeBHist F)
                                                  (openPhysicalFitDecodeBHist E)
                                                  (openPhysicalFitDecodeBHist L)
                                                  (openPhysicalFitDecodeBHist R)
                                                  (openPhysicalFitDecodeBHist N))
                                          | _ :: _ => none

private theorem openPhysicalFit_round_trip :
    ∀ x : OpenPhysicalFitUp,
      openPhysicalFitFromEventFlow (openPhysicalFitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H Pi O M C F E L R N =>
      change
        some
          (OpenPhysicalFitUp.mk
            (openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist H))
            (openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist Pi))
            (openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist O))
            (openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist M))
            (openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist C))
            (openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist F))
            (openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist E))
            (openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist L))
            (openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist R))
            (openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist N))) =
        some (OpenPhysicalFitUp.mk H Pi O M C F E L R N)
      rw [openPhysicalFitDecode_encode_bhist H, openPhysicalFitDecode_encode_bhist Pi,
        openPhysicalFitDecode_encode_bhist O, openPhysicalFitDecode_encode_bhist M,
        openPhysicalFitDecode_encode_bhist C, openPhysicalFitDecode_encode_bhist F,
        openPhysicalFitDecode_encode_bhist E, openPhysicalFitDecode_encode_bhist L,
        openPhysicalFitDecode_encode_bhist R, openPhysicalFitDecode_encode_bhist N]

theorem openPhysicalFitToEventFlow_injective {x y : OpenPhysicalFitUp} :
    openPhysicalFitToEventFlow x = openPhysicalFitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk H1 Pi1 O1 M1 C1 F1 E1 L1 R1 N1 =>
      cases y with
      | mk H2 Pi2 O2 M2 C2 F2 E2 L2 R2 N2 =>
          injection heq with hH tail1
          injection tail1 with hPi tail2
          injection tail2 with hO tail3
          injection tail3 with hM tail4
          injection tail4 with hC tail5
          injection tail5 with hF tail6
          injection tail6 with hE tail7
          injection tail7 with hL tail8
          injection tail8 with hR tail9
          injection tail9 with hN _
          have hH' : H1 = H2 := by
            have decoded := congrArg openPhysicalFitDecodeBHist hH
            exact Eq.trans (openPhysicalFitDecode_encode_bhist H1).symm
              (Eq.trans decoded (openPhysicalFitDecode_encode_bhist H2))
          cases hH'
          have hPi' : Pi1 = Pi2 := by
            have decoded := congrArg openPhysicalFitDecodeBHist hPi
            exact Eq.trans (openPhysicalFitDecode_encode_bhist Pi1).symm
              (Eq.trans decoded (openPhysicalFitDecode_encode_bhist Pi2))
          cases hPi'
          have hO' : O1 = O2 := by
            have decoded := congrArg openPhysicalFitDecodeBHist hO
            exact Eq.trans (openPhysicalFitDecode_encode_bhist O1).symm
              (Eq.trans decoded (openPhysicalFitDecode_encode_bhist O2))
          cases hO'
          have hM' : M1 = M2 := by
            have decoded := congrArg openPhysicalFitDecodeBHist hM
            exact Eq.trans (openPhysicalFitDecode_encode_bhist M1).symm
              (Eq.trans decoded (openPhysicalFitDecode_encode_bhist M2))
          cases hM'
          have hC' : C1 = C2 := by
            have decoded := congrArg openPhysicalFitDecodeBHist hC
            exact Eq.trans (openPhysicalFitDecode_encode_bhist C1).symm
              (Eq.trans decoded (openPhysicalFitDecode_encode_bhist C2))
          cases hC'
          have hF' : F1 = F2 := by
            have decoded := congrArg openPhysicalFitDecodeBHist hF
            exact Eq.trans (openPhysicalFitDecode_encode_bhist F1).symm
              (Eq.trans decoded (openPhysicalFitDecode_encode_bhist F2))
          cases hF'
          have hE' : E1 = E2 := by
            have decoded := congrArg openPhysicalFitDecodeBHist hE
            exact Eq.trans (openPhysicalFitDecode_encode_bhist E1).symm
              (Eq.trans decoded (openPhysicalFitDecode_encode_bhist E2))
          cases hE'
          have hL' : L1 = L2 := by
            have decoded := congrArg openPhysicalFitDecodeBHist hL
            exact Eq.trans (openPhysicalFitDecode_encode_bhist L1).symm
              (Eq.trans decoded (openPhysicalFitDecode_encode_bhist L2))
          cases hL'
          have hR' : R1 = R2 := by
            have decoded := congrArg openPhysicalFitDecodeBHist hR
            exact Eq.trans (openPhysicalFitDecode_encode_bhist R1).symm
              (Eq.trans decoded (openPhysicalFitDecode_encode_bhist R2))
          cases hR'
          have hN' : N1 = N2 := by
            have decoded := congrArg openPhysicalFitDecodeBHist hN
            exact Eq.trans (openPhysicalFitDecode_encode_bhist N1).symm
              (Eq.trans decoded (openPhysicalFitDecode_encode_bhist N2))
          cases hN'
          rfl

def openPhysicalFitExplicitBHistCarrier : BHistCarrier OpenPhysicalFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := openPhysicalFitToEventFlow
  fromEventFlow := openPhysicalFitFromEventFlow

def openPhysicalFitExplicitChapterTasteGate :
    @ChapterTasteGate OpenPhysicalFitUp openPhysicalFitExplicitBHistCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  letI : BHistCarrier OpenPhysicalFitUp := openPhysicalFitExplicitBHistCarrier
  {
    round_trip := by
      intro x
      change openPhysicalFitFromEventFlow (openPhysicalFitToEventFlow x) = some x
      exact openPhysicalFit_round_trip x
    layer_separation := by
      intro x y hxy heq
      exact hxy (openPhysicalFitToEventFlow_injective heq)
  }

def openPhysicalFitExplicitFieldFaithful :
    @FieldFaithful OpenPhysicalFitUp openPhysicalFitExplicitBHistCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  letI : BHistCarrier OpenPhysicalFitUp := openPhysicalFitExplicitBHistCarrier
  {
    fields := fun x =>
      match x with
      | OpenPhysicalFitUp.mk H Pi O M C F E L R N => [H, Pi, O, M, C, F, E, L, R, N]
    field_faithful := by
      -- BEDC touchpoint anchor: BHist BMark
      intro x y h
      cases x with
      | mk H1 Pi1 O1 M1 C1 F1 E1 L1 R1 N1 =>
          cases y with
          | mk H2 Pi2 O2 M2 C2 F2 E2 L2 R2 N2 =>
              change
                [H1, Pi1, O1, M1, C1, F1, E1, L1, R1, N1] =
                  [H2, Pi2, O2, M2, C2, F2, E2, L2, R2, N2] at h
              cases h
              rfl
  }

instance openPhysicalFitBHistCarrier : BHistCarrier OpenPhysicalFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := openPhysicalFitToEventFlow
  fromEventFlow := openPhysicalFitFromEventFlow

instance openPhysicalFitChapterTasteGate : ChapterTasteGate OpenPhysicalFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change openPhysicalFitFromEventFlow (openPhysicalFitToEventFlow x) = some x
    exact openPhysicalFit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (openPhysicalFitToEventFlow_injective heq)

instance openPhysicalFitFieldFaithful : FieldFaithful OpenPhysicalFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | OpenPhysicalFitUp.mk H Pi O M C F E L R N => [H, Pi, O, M, C, F, E, L, R, N]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk H1 Pi1 O1 M1 C1 F1 E1 L1 R1 N1 =>
        cases y with
        | mk H2 Pi2 O2 M2 C2 F2 E2 L2 R2 N2 =>
            change
              [H1, Pi1, O1, M1, C1, F1, E1, L1, R1, N1] =
                [H2, Pi2, O2, M2, C2, F2, E2, L2, R2, N2] at h
            cases h
            rfl

instance openPhysicalFitNontrivial : Nontrivial OpenPhysicalFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OpenPhysicalFitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OpenPhysicalFitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem OpenPhysicalFitTasteGate_single_carrier_alignment :
    (∀ h : BHist, openPhysicalFitDecodeBHist (openPhysicalFitEncodeBHist h) = h) ∧
      (∀ x : OpenPhysicalFitUp,
        openPhysicalFitFromEventFlow (openPhysicalFitToEventFlow x) = some x) ∧
        (∀ x y : OpenPhysicalFitUp,
          openPhysicalFitToEventFlow x = openPhysicalFitToEventFlow y → x = y) ∧
          Nonempty (@ChapterTasteGate OpenPhysicalFitUp openPhysicalFitExplicitBHistCarrier) ∧
            Nonempty (@FieldFaithful OpenPhysicalFitUp openPhysicalFitExplicitBHistCarrier) ∧
              openPhysicalFitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact openPhysicalFitDecode_encode_bhist
  · constructor
    · exact openPhysicalFit_round_trip
    · constructor
      · intro x y heq
        exact openPhysicalFitToEventFlow_injective heq
      · constructor
        · exact Nonempty.intro openPhysicalFitExplicitChapterTasteGate
        · constructor
          · exact Nonempty.intro openPhysicalFitExplicitFieldFaithful
          · rfl

theorem OpenPhysicalFit_semantic_name_certificate {H Pi O M C F E L R N : BHist} :
    SemanticNameCert
      (fun row : BHist =>
        hsame row H ∨ hsame row Pi ∨ hsame row O ∨ hsame row M ∨ hsame row C ∨
          hsame row F ∨ hsame row E ∨ hsame row L ∨ hsame row R ∨ hsame row N)
      (fun row : BHist =>
        hsame row H ∨ hsame row Pi ∨ hsame row O ∨ hsame row M ∨ hsame row C ∨
          hsame row F ∨ hsame row E ∨ hsame row L ∨ hsame row R ∨ hsame row N)
      (fun row : BHist =>
        hsame row H ∨ hsame row Pi ∨ hsame row O ∨ hsame row M ∨ hsame row C ∨
          hsame row F ∨ hsame row E ∨ hsame row L ∨ hsame row R ∨ hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro H (Or.inl (hsame_refl H))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        have rowEq : row = row' := hsame_iff_eq.mp sameRows
        cases rowEq
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.OpenPhysicalFitUp
