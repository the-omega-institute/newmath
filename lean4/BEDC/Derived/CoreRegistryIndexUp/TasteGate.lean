import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CoreRegistryIndexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CoreRegistryIndexUp : Type where
  | mk
      (C T G D S F U O A H K P N : BHist) :
      CoreRegistryIndexUp
  deriving DecidableEq

def coreRegistryIndexEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: coreRegistryIndexEncodeBHist h
  | BHist.e1 h => BMark.b1 :: coreRegistryIndexEncodeBHist h

def coreRegistryIndexDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (coreRegistryIndexDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (coreRegistryIndexDecodeBHist tail)

private theorem coreRegistryIndexDecode_encode_bhist :
    ∀ h : BHist,
      coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem coreRegistryIndex_mk_congr
    {C C' T T' G G' D D' S S' F F' U U' O O' A A' H H' K K' P P' N N' :
      BHist}
    (hC : C' = C) (hT : T' = T) (hG : G' = G) (hD : D' = D)
    (hS : S' = S) (hF : F' = F) (hU : U' = U) (hO : O' = O)
    (hA : A' = A) (hH : H' = H) (hK : K' = K) (hP : P' = P)
    (hN : N' = N) :
    CoreRegistryIndexUp.mk C' T' G' D' S' F' U' O' A' H' K' P' N' =
      CoreRegistryIndexUp.mk C T G D S F U O A H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hC
  cases hT
  cases hG
  cases hD
  cases hS
  cases hF
  cases hU
  cases hO
  cases hA
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

def coreRegistryIndexToEventFlow : CoreRegistryIndexUp → EventFlow
  | CoreRegistryIndexUp.mk C T G D S F U O A H K P N =>
      [[BMark.b0],
        coreRegistryIndexEncodeBHist C,
        [BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        coreRegistryIndexEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        coreRegistryIndexEncodeBHist N]

def coreRegistryIndexFromEventFlow : EventFlow → Option CoreRegistryIndexUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | C :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | G :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | S :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | F :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | U :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | O :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | A :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | H :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | K :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | P :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | N :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (CoreRegistryIndexUp.mk
                                                                                                                  (coreRegistryIndexDecodeBHist C)
                                                                                                                  (coreRegistryIndexDecodeBHist T)
                                                                                                                  (coreRegistryIndexDecodeBHist G)
                                                                                                                  (coreRegistryIndexDecodeBHist D)
                                                                                                                  (coreRegistryIndexDecodeBHist S)
                                                                                                                  (coreRegistryIndexDecodeBHist F)
                                                                                                                  (coreRegistryIndexDecodeBHist U)
                                                                                                                  (coreRegistryIndexDecodeBHist O)
                                                                                                                  (coreRegistryIndexDecodeBHist A)
                                                                                                                  (coreRegistryIndexDecodeBHist H)
                                                                                                                  (coreRegistryIndexDecodeBHist K)
                                                                                                                  (coreRegistryIndexDecodeBHist P)
                                                                                                                  (coreRegistryIndexDecodeBHist N))
                                                                                                          | _ :: _ => none

private theorem coreRegistryIndex_round_trip :
    ∀ x : CoreRegistryIndexUp,
      coreRegistryIndexFromEventFlow (coreRegistryIndexToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C T G D S F U O A H K P N =>
      change
        some
          (CoreRegistryIndexUp.mk
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist C))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist T))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist G))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist D))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist S))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist F))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist U))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist O))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist A))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist H))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist K))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist P))
            (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist N))) =
          some (CoreRegistryIndexUp.mk C T G D S F U O A H K P N)
      exact
        congrArg some
          (coreRegistryIndex_mk_congr
            (coreRegistryIndexDecode_encode_bhist C)
            (coreRegistryIndexDecode_encode_bhist T)
            (coreRegistryIndexDecode_encode_bhist G)
            (coreRegistryIndexDecode_encode_bhist D)
            (coreRegistryIndexDecode_encode_bhist S)
            (coreRegistryIndexDecode_encode_bhist F)
            (coreRegistryIndexDecode_encode_bhist U)
            (coreRegistryIndexDecode_encode_bhist O)
            (coreRegistryIndexDecode_encode_bhist A)
            (coreRegistryIndexDecode_encode_bhist H)
            (coreRegistryIndexDecode_encode_bhist K)
            (coreRegistryIndexDecode_encode_bhist P)
            (coreRegistryIndexDecode_encode_bhist N))

private theorem coreRegistryIndexToEventFlow_injective
    {x y : CoreRegistryIndexUp} :
    coreRegistryIndexToEventFlow x = coreRegistryIndexToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      coreRegistryIndexFromEventFlow (coreRegistryIndexToEventFlow x) =
        coreRegistryIndexFromEventFlow (coreRegistryIndexToEventFlow y) :=
    congrArg coreRegistryIndexFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (coreRegistryIndex_round_trip x).symm
      (Eq.trans hread (coreRegistryIndex_round_trip y)))

def coreRegistryIndexFields : CoreRegistryIndexUp → List BHist
  | CoreRegistryIndexUp.mk C T G D S F U O A H K P N =>
      [C, T, G, D, S, F, U, O, A, H, K, P, N]

private theorem coreRegistryIndex_field_faithful :
    ∀ x y : CoreRegistryIndexUp,
      coreRegistryIndexFields x = coreRegistryIndexFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C1 T1 G1 D1 S1 F1 U1 O1 A1 H1 K1 P1 N1 =>
      cases y with
      | mk C2 T2 G2 D2 S2 F2 U2 O2 A2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance coreRegistryIndexBHistCarrier : BHistCarrier CoreRegistryIndexUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := coreRegistryIndexToEventFlow
  fromEventFlow := coreRegistryIndexFromEventFlow

instance coreRegistryIndexChapterTasteGate : ChapterTasteGate CoreRegistryIndexUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change coreRegistryIndexFromEventFlow (coreRegistryIndexToEventFlow x) = some x
    exact coreRegistryIndex_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (coreRegistryIndexToEventFlow_injective heq)

instance coreRegistryIndexFieldFaithful : FieldFaithful CoreRegistryIndexUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := coreRegistryIndexFields
  field_faithful := coreRegistryIndex_field_faithful

def taste_gate : ChapterTasteGate CoreRegistryIndexUp :=
  -- BEDC touchpoint anchor: BHist BMark
  coreRegistryIndexChapterTasteGate

theorem CoreRegistryIndexTasteGate_single_carrier_alignment :
    (∀ h : BHist, coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist h) = h) ∧
      (∀ x : CoreRegistryIndexUp,
        coreRegistryIndexFromEventFlow (coreRegistryIndexToEventFlow x) = some x) ∧
      (∀ x y : CoreRegistryIndexUp,
        coreRegistryIndexToEventFlow x = coreRegistryIndexToEventFlow y → x = y) ∧
      coreRegistryIndexEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk C T G D S F U O A H K P N =>
          change
            some
              (CoreRegistryIndexUp.mk
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist C))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist T))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist G))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist D))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist S))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist F))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist U))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist O))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist A))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist H))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist K))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist P))
                (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist N))) =
              some (CoreRegistryIndexUp.mk C T G D S F U O A H K P N)
          exact
            congrArg some
              (coreRegistryIndex_mk_congr
                (coreRegistryIndexDecode_encode_bhist C)
                (coreRegistryIndexDecode_encode_bhist T)
                (coreRegistryIndexDecode_encode_bhist G)
                (coreRegistryIndexDecode_encode_bhist D)
                (coreRegistryIndexDecode_encode_bhist S)
                (coreRegistryIndexDecode_encode_bhist F)
                (coreRegistryIndexDecode_encode_bhist U)
                (coreRegistryIndexDecode_encode_bhist O)
                (coreRegistryIndexDecode_encode_bhist A)
                (coreRegistryIndexDecode_encode_bhist H)
                (coreRegistryIndexDecode_encode_bhist K)
                (coreRegistryIndexDecode_encode_bhist P)
                (coreRegistryIndexDecode_encode_bhist N))
    · constructor
      · intro x y heq
        have hx :
            coreRegistryIndexFromEventFlow (coreRegistryIndexToEventFlow x) = some x := by
          cases x with
          | mk C T G D S F U O A H K P N =>
              change
                some
                  (CoreRegistryIndexUp.mk
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist C))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist T))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist G))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist D))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist S))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist F))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist U))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist O))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist A))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist H))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist K))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist P))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist N))) =
                  some (CoreRegistryIndexUp.mk C T G D S F U O A H K P N)
              exact
                congrArg some
                  (coreRegistryIndex_mk_congr
                    (coreRegistryIndexDecode_encode_bhist C)
                    (coreRegistryIndexDecode_encode_bhist T)
                    (coreRegistryIndexDecode_encode_bhist G)
                    (coreRegistryIndexDecode_encode_bhist D)
                    (coreRegistryIndexDecode_encode_bhist S)
                    (coreRegistryIndexDecode_encode_bhist F)
                    (coreRegistryIndexDecode_encode_bhist U)
                    (coreRegistryIndexDecode_encode_bhist O)
                    (coreRegistryIndexDecode_encode_bhist A)
                    (coreRegistryIndexDecode_encode_bhist H)
                    (coreRegistryIndexDecode_encode_bhist K)
                    (coreRegistryIndexDecode_encode_bhist P)
                    (coreRegistryIndexDecode_encode_bhist N))
        have hy :
            coreRegistryIndexFromEventFlow (coreRegistryIndexToEventFlow y) = some y := by
          cases y with
          | mk C T G D S F U O A H K P N =>
              change
                some
                  (CoreRegistryIndexUp.mk
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist C))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist T))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist G))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist D))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist S))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist F))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist U))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist O))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist A))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist H))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist K))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist P))
                    (coreRegistryIndexDecodeBHist (coreRegistryIndexEncodeBHist N))) =
                  some (CoreRegistryIndexUp.mk C T G D S F U O A H K P N)
              exact
                congrArg some
                  (coreRegistryIndex_mk_congr
                    (coreRegistryIndexDecode_encode_bhist C)
                    (coreRegistryIndexDecode_encode_bhist T)
                    (coreRegistryIndexDecode_encode_bhist G)
                    (coreRegistryIndexDecode_encode_bhist D)
                    (coreRegistryIndexDecode_encode_bhist S)
                    (coreRegistryIndexDecode_encode_bhist F)
                    (coreRegistryIndexDecode_encode_bhist U)
                    (coreRegistryIndexDecode_encode_bhist O)
                    (coreRegistryIndexDecode_encode_bhist A)
                    (coreRegistryIndexDecode_encode_bhist H)
                    (coreRegistryIndexDecode_encode_bhist K)
                    (coreRegistryIndexDecode_encode_bhist P)
                    (coreRegistryIndexDecode_encode_bhist N))
        have hread :
            coreRegistryIndexFromEventFlow (coreRegistryIndexToEventFlow x) =
              coreRegistryIndexFromEventFlow (coreRegistryIndexToEventFlow y) :=
          congrArg coreRegistryIndexFromEventFlow heq
        exact Option.some.inj (Eq.trans hx.symm (Eq.trans hread hy))
      · rfl

theorem CoreRegistryIndex_refusal_audit_nonescape_certificate [AskSetup] [PackageSetup]
    {C T G D S F U O A H K P N refusalRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle F pkg ->
      PkgSig bundle A pkg ->
        hsame refusalRead F ->
          hsame auditRead A ->
            coreRegistryIndexFields (CoreRegistryIndexUp.mk C T G D S F U O A H K P N) =
                [C, T, G, D, S, F, U, O, A, H, K, P, N] ∧
              SemanticNameCert
                (fun row : BHist =>
                  hsame row refusalRead ∨ hsame row auditRead ∨ hsame row F ∨
                    hsame row A)
                (fun row : BHist =>
                  hsame row refusalRead ∨ hsame row auditRead ∨ hsame row F ∨
                    hsame row A)
                (fun row : BHist =>
                  (hsame row F ∧ PkgSig bundle F pkg) ∨
                    (hsame row A ∧ PkgSig bundle A pkg))
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame
  intro pkgF pkgA refusalSame auditSame
  have sourceRefusal :
      (fun row : BHist =>
        hsame row refusalRead ∨ hsame row auditRead ∨ hsame row F ∨ hsame row A)
        refusalRead := by
    exact Or.inl (hsame_refl refusalRead)
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row refusalRead ∨ hsame row auditRead ∨ hsame row F ∨ hsame row A)
        (fun row : BHist =>
          hsame row refusalRead ∨ hsame row auditRead ∨ hsame row F ∨ hsame row A)
        (fun row : BHist =>
          (hsame row F ∧ PkgSig bundle F pkg) ∨
            (hsame row A ∧ PkgSig bundle A pkg))
        hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceRefusal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        cases source with
        | inl rowRefusal =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowRefusal)
        | inr tail =>
            cases tail with
            | inl rowAudit =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowAudit))
            | inr tail =>
                cases tail with
                | inl rowF =>
                    exact
                      Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowF)))
                | inr rowA =>
                    exact
                      Or.inr
                        (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowA)))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      cases source with
      | inl rowRefusal =>
          exact Or.inl ⟨hsame_trans rowRefusal refusalSame, pkgF⟩
      | inr tail =>
          cases tail with
          | inl rowAudit =>
              exact Or.inr ⟨hsame_trans rowAudit auditSame, pkgA⟩
          | inr tail =>
              cases tail with
              | inl rowF =>
                  exact Or.inl ⟨rowF, pkgF⟩
              | inr rowA =>
                  exact Or.inr ⟨rowA, pkgA⟩
  }
  exact ⟨rfl, cert⟩

end BEDC.Derived.CoreRegistryIndexUp
