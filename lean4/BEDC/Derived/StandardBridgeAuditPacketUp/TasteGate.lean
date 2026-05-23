import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StandardBridgeAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StandardBridgeAuditPacketUp : Type where
  | mk : (N T E D R U P L H C Q : BHist) → StandardBridgeAuditPacketUp
  deriving DecidableEq

def standardBridgeAuditPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: standardBridgeAuditPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: standardBridgeAuditPacketEncodeBHist h

def standardBridgeAuditPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (standardBridgeAuditPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (standardBridgeAuditPacketDecodeBHist tail)

private theorem standardBridgeAuditPacketDecode_encode_bhist :
    ∀ h : BHist,
      standardBridgeAuditPacketDecodeBHist
        (standardBridgeAuditPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem standardBridgeAuditPacket_mk_congr
    {N N' T T' E E' D D' R R' U U' P P' L L' H H' C C' Q Q' : BHist}
    (hN : N' = N) (hT : T' = T) (hE : E' = E) (hD : D' = D) (hR : R' = R)
    (hU : U' = U) (hP : P' = P) (hL : L' = L) (hH : H' = H) (hC : C' = C)
    (hQ : Q' = Q) :
    StandardBridgeAuditPacketUp.mk N' T' E' D' R' U' P' L' H' C' Q' =
      StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hN
  cases hT
  cases hE
  cases hD
  cases hR
  cases hU
  cases hP
  cases hL
  cases hH
  cases hC
  cases hQ
  rfl

def standardBridgeAuditPacketToEventFlow : StandardBridgeAuditPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q =>
      [[BMark.b0],
        standardBridgeAuditPacketEncodeBHist N,
        [BMark.b1, BMark.b0],
        standardBridgeAuditPacketEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        standardBridgeAuditPacketEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        standardBridgeAuditPacketEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        standardBridgeAuditPacketEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        standardBridgeAuditPacketEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        standardBridgeAuditPacketEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        standardBridgeAuditPacketEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        standardBridgeAuditPacketEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        standardBridgeAuditPacketEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        standardBridgeAuditPacketEncodeBHist Q]

def standardBridgeAuditPacketFromEventFlow :
    EventFlow → Option StandardBridgeAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: N :: _tag1 :: T :: _tag2 :: E :: _tag3 :: D :: _tag4 :: R ::
      _tag5 :: U :: _tag6 :: P :: _tag7 :: L :: _tag8 :: H :: _tag9 :: C ::
        _tag10 :: Q :: [] =>
      some
        (StandardBridgeAuditPacketUp.mk
          (standardBridgeAuditPacketDecodeBHist N)
          (standardBridgeAuditPacketDecodeBHist T)
          (standardBridgeAuditPacketDecodeBHist E)
          (standardBridgeAuditPacketDecodeBHist D)
          (standardBridgeAuditPacketDecodeBHist R)
          (standardBridgeAuditPacketDecodeBHist U)
          (standardBridgeAuditPacketDecodeBHist P)
          (standardBridgeAuditPacketDecodeBHist L)
          (standardBridgeAuditPacketDecodeBHist H)
          (standardBridgeAuditPacketDecodeBHist C)
          (standardBridgeAuditPacketDecodeBHist Q))
  | _ => none

private theorem standardBridgeAuditPacket_round_trip :
    ∀ x : StandardBridgeAuditPacketUp,
      standardBridgeAuditPacketFromEventFlow
        (standardBridgeAuditPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N T E D R U P L H C Q =>
      change
        some
          (StandardBridgeAuditPacketUp.mk
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist N))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist T))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist E))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist D))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist R))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist U))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist P))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist L))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist H))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist C))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist Q))) =
          some (StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q)
      exact
        congrArg some
          (standardBridgeAuditPacket_mk_congr
            (standardBridgeAuditPacketDecode_encode_bhist N)
            (standardBridgeAuditPacketDecode_encode_bhist T)
            (standardBridgeAuditPacketDecode_encode_bhist E)
            (standardBridgeAuditPacketDecode_encode_bhist D)
            (standardBridgeAuditPacketDecode_encode_bhist R)
            (standardBridgeAuditPacketDecode_encode_bhist U)
            (standardBridgeAuditPacketDecode_encode_bhist P)
            (standardBridgeAuditPacketDecode_encode_bhist L)
            (standardBridgeAuditPacketDecode_encode_bhist H)
            (standardBridgeAuditPacketDecode_encode_bhist C)
            (standardBridgeAuditPacketDecode_encode_bhist Q))

private theorem standardBridgeAuditPacketToEventFlow_injective
    {x y : StandardBridgeAuditPacketUp} :
    standardBridgeAuditPacketToEventFlow x =
      standardBridgeAuditPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      standardBridgeAuditPacketFromEventFlow
          (standardBridgeAuditPacketToEventFlow x) =
        standardBridgeAuditPacketFromEventFlow
          (standardBridgeAuditPacketToEventFlow y) :=
    congrArg standardBridgeAuditPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (standardBridgeAuditPacket_round_trip x).symm
      (Eq.trans hread (standardBridgeAuditPacket_round_trip y)))

instance standardBridgeAuditPacketBHistCarrier :
    BHistCarrier StandardBridgeAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := standardBridgeAuditPacketToEventFlow
  fromEventFlow := standardBridgeAuditPacketFromEventFlow

instance standardBridgeAuditPacketChapterTasteGate :
    ChapterTasteGate StandardBridgeAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      standardBridgeAuditPacketFromEventFlow
        (standardBridgeAuditPacketToEventFlow x) = some x
    exact standardBridgeAuditPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (standardBridgeAuditPacketToEventFlow_injective heq)

instance standardBridgeAuditPacketFieldFaithful :
    FieldFaithful StandardBridgeAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q => [N, T, E, D, R, U, P, L, H, C, Q]
  field_faithful := by
    intro x y h
    cases x with
    | mk N₁ T₁ E₁ D₁ R₁ U₁ P₁ L₁ H₁ C₁ Q₁ =>
        cases y with
        | mk N₂ T₂ E₂ D₂ R₂ U₂ P₂ L₂ H₂ C₂ Q₂ =>
            injection h with hN hRest₁
            injection hRest₁ with hT hRest₂
            injection hRest₂ with hE hRest₃
            injection hRest₃ with hD hRest₄
            injection hRest₄ with hR hRest₅
            injection hRest₅ with hU hRest₆
            injection hRest₆ with hP hRest₇
            injection hRest₇ with hL hRest₈
            injection hRest₈ with hH hRest₉
            injection hRest₉ with hC hRest₁₀
            injection hRest₁₀ with hQ _
            cases hN
            cases hT
            cases hE
            cases hD
            cases hR
            cases hU
            cases hP
            cases hL
            cases hH
            cases hC
            cases hQ
            rfl

instance standardBridgeAuditPacketNontrivial :
    Nontrivial StandardBridgeAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StandardBridgeAuditPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      StandardBridgeAuditPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StandardBridgeAuditPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  standardBridgeAuditPacketChapterTasteGate

def StandardBridgeAuditPacket_round_trip_rows_visible_fields :
    StandardBridgeAuditPacketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q => [N, T, E, D, R, U, P, L, H, C, Q]

def StandardBridgeAuditPacket_round_trip_rows_visible_readback :
    StandardBridgeAuditPacketUp → Option StandardBridgeAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q =>
      some
        (StandardBridgeAuditPacketUp.mk
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist N))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist T))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist E))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist D))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist R))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist U))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist P))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist L))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist H))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist C))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist Q)))

theorem StandardBridgeAuditPacket_round_trip_rows_visible (N T E D R U P L H C Q : BHist) :
    StandardBridgeAuditPacket_round_trip_rows_visible_readback
        (StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q) =
      some (StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q) ∧
      StandardBridgeAuditPacket_round_trip_rows_visible_fields
          (StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q) =
        [N, T, E, D, R, U, P, L, H, C, Q] ∧
        standardBridgeAuditPacketEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  have hN :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist N) = N := by
    induction N with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hT :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist T) = T := by
    induction T with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hE :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist E) = E := by
    induction E with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hD :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist D) = D := by
    induction D with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hR :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist R) = R := by
    induction R with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hU :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist U) = U := by
    induction U with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hP :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist P) = P := by
    induction P with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hL :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist L) = L := by
    induction L with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hH :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist H) = H := by
    induction H with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hC :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist C) = C := by
    induction C with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hQ :
      standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist Q) = Q := by
    induction Q with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · change
      some
        (StandardBridgeAuditPacketUp.mk
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist N))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist T))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist E))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist D))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist R))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist U))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist P))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist L))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist H))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist C))
          (standardBridgeAuditPacketDecodeBHist (standardBridgeAuditPacketEncodeBHist Q))) =
        some (StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q)
    rw [hN, hT, hE, hD, hR, hU, hP, hL, hH, hC, hQ]
  · exact ⟨rfl, rfl⟩

theorem StandardBridgeAuditPacketTasteGate_obligation :
    (∀ x y : StandardBridgeAuditPacketUp,
        StandardBridgeAuditPacket_round_trip_rows_visible_fields x =
          StandardBridgeAuditPacket_round_trip_rows_visible_fields y → x = y) ∧
      (∀ h : BHist, standardBridgeAuditPacketDecodeBHist
        (standardBridgeAuditPacketEncodeBHist h) = h) ∧
        ∀ N T E D R U P L H C Q : BHist,
          StandardBridgeAuditPacket_round_trip_rows_visible_readback
              (StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q) =
            some (StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · intro x y h
    cases x with
    | mk N₁ T₁ E₁ D₁ R₁ U₁ P₁ L₁ H₁ C₁ Q₁ =>
        cases y with
        | mk N₂ T₂ E₂ D₂ R₂ U₂ P₂ L₂ H₂ C₂ Q₂ =>
            cases h
            rfl
  · constructor
    · exact standardBridgeAuditPacketDecode_encode_bhist
    · intro N T E D R U P L H C Q
      exact (StandardBridgeAuditPacket_round_trip_rows_visible N T E D R U P L H C Q).left

theorem StandardBridgeAuditPacket_theorem_preservation_ledger
    {N T E D R U P L H C Q theoremRow counterpartRow translatedRow : BHist} :
    Cont U L C →
      Cont L P C →
        Cont U translatedRow C →
          hsame theoremRow U →
            hsame counterpartRow translatedRow →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row theoremRow ∧
                    ∃ packet : StandardBridgeAuditPacketUp,
                      packet = StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q)
                (fun row : BHist =>
                  Cont U L C ∧ Cont L P C ∧ Cont U translatedRow C ∧ hsame row theoremRow)
                (fun row : BHist =>
                  hsame row theoremRow ∧ hsame counterpartRow translatedRow ∧ hsame P P ∧
                    hsame Q Q)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro contUL contLP contUTranslated sameTheorem sameCounterpart
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro theoremRow
          (And.intro (hsame_refl theoremRow)
            (Exists.intro (StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q) rfl))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            source.right
    }
    pattern_sound := by
      intro row source
      exact ⟨contUL, contLP, contUTranslated, source.left⟩
    ledger_sound := by
      intro row source
      exact
        ⟨source.left, sameCounterpart, hsame_refl P, hsame_refl Q⟩
  }

theorem StandardBridgeAuditPacket_nonhost_leak_certificate
    {N T E D R U P L H C Q bridgeRead : BHist} :
    Cont E D R →
      Cont R P bridgeRead →
        Cont P L H →
          SemanticNameCert
            (fun row : BHist =>
              hsame row bridgeRead ∧
                ∃ packet : StandardBridgeAuditPacketUp,
                  packet = StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q)
            (fun row : BHist => Cont E D R ∧ Cont R P row ∧ Cont P L H)
            (fun row : BHist => hsame row bridgeRead ∧ hsame P P ∧ hsame Q Q)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro encodeDecode roundTripToPublic noHostLedger
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead
          (And.intro (hsame_refl bridgeRead)
            (Exists.intro (StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q) rfl))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            source.right
    }
    pattern_sound := by
      intro row source
      have publicRoute : Cont R P row := by
        cases source.left
        exact roundTripToPublic
      exact
        ⟨encodeDecode, publicRoute, noHostLedger⟩
    ledger_sound := by
      intro row source
      exact ⟨source.left, hsame_refl P, hsame_refl Q⟩
  }

end BEDC.Derived.StandardBridgeAuditPacketUp
