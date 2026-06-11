import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanOrderedFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanOrderedFieldUp : Type where
  | mk : (R A Q O B H C P N : BHist) → ArchimedeanOrderedFieldUp
  deriving DecidableEq

def archimedeanOrderedFieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanOrderedFieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanOrderedFieldEncodeBHist h

def archimedeanOrderedFieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanOrderedFieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanOrderedFieldDecodeBHist tail)

private theorem archimedeanOrderedFieldDecode_encode_bhist :
    ∀ h : BHist,
      archimedeanOrderedFieldDecodeBHist
        (archimedeanOrderedFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanOrderedFieldToEventFlow : ArchimedeanOrderedFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanOrderedFieldUp.mk R A Q O B H C P N =>
      [[BMark.b0],
        archimedeanOrderedFieldEncodeBHist R,
        [BMark.b1, BMark.b0],
        archimedeanOrderedFieldEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        archimedeanOrderedFieldEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        archimedeanOrderedFieldEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        archimedeanOrderedFieldEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        archimedeanOrderedFieldEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        archimedeanOrderedFieldEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        archimedeanOrderedFieldEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        archimedeanOrderedFieldEncodeBHist N]

def archimedeanOrderedFieldFromEventFlow :
    EventFlow → Option ArchimedeanOrderedFieldUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: rest0 =>
      match rest0 with
      | R :: rest1 =>
          match rest1 with
          | _tag1 :: rest2 =>
              match rest2 with
              | A :: rest3 =>
                  match rest3 with
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | Q :: rest5 =>
                          match rest5 with
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | O :: rest7 =>
                                  match rest7 with
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | B :: rest9 =>
                                          match rest9 with
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ArchimedeanOrderedFieldUp.mk
                                                                                  (archimedeanOrderedFieldDecodeBHist R)
                                                                                  (archimedeanOrderedFieldDecodeBHist A)
                                                                                  (archimedeanOrderedFieldDecodeBHist Q)
                                                                                  (archimedeanOrderedFieldDecodeBHist O)
                                                                                  (archimedeanOrderedFieldDecodeBHist B)
                                                                                  (archimedeanOrderedFieldDecodeBHist H)
                                                                                  (archimedeanOrderedFieldDecodeBHist C)
                                                                                  (archimedeanOrderedFieldDecodeBHist P)
                                                                                  (archimedeanOrderedFieldDecodeBHist N))
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
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

def archimedeanOrderedFieldFields :
    ArchimedeanOrderedFieldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanOrderedFieldUp.mk R A Q O B H C P N =>
      [R, A, Q, O, B, H, C, P, N]

private theorem archimedeanOrderedField_round_trip :
    ∀ x : ArchimedeanOrderedFieldUp,
      archimedeanOrderedFieldFromEventFlow
        (archimedeanOrderedFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R A Q O B H C P N =>
      change
        some
          (ArchimedeanOrderedFieldUp.mk
            (archimedeanOrderedFieldDecodeBHist
              (archimedeanOrderedFieldEncodeBHist R))
            (archimedeanOrderedFieldDecodeBHist
              (archimedeanOrderedFieldEncodeBHist A))
            (archimedeanOrderedFieldDecodeBHist
              (archimedeanOrderedFieldEncodeBHist Q))
            (archimedeanOrderedFieldDecodeBHist
              (archimedeanOrderedFieldEncodeBHist O))
            (archimedeanOrderedFieldDecodeBHist
              (archimedeanOrderedFieldEncodeBHist B))
            (archimedeanOrderedFieldDecodeBHist
              (archimedeanOrderedFieldEncodeBHist H))
            (archimedeanOrderedFieldDecodeBHist
              (archimedeanOrderedFieldEncodeBHist C))
            (archimedeanOrderedFieldDecodeBHist
              (archimedeanOrderedFieldEncodeBHist P))
            (archimedeanOrderedFieldDecodeBHist
              (archimedeanOrderedFieldEncodeBHist N))) =
          some (ArchimedeanOrderedFieldUp.mk R A Q O B H C P N)
      rw [archimedeanOrderedFieldDecode_encode_bhist R,
        archimedeanOrderedFieldDecode_encode_bhist A,
        archimedeanOrderedFieldDecode_encode_bhist Q,
        archimedeanOrderedFieldDecode_encode_bhist O,
        archimedeanOrderedFieldDecode_encode_bhist B,
        archimedeanOrderedFieldDecode_encode_bhist H,
        archimedeanOrderedFieldDecode_encode_bhist C,
        archimedeanOrderedFieldDecode_encode_bhist P,
        archimedeanOrderedFieldDecode_encode_bhist N]

private theorem archimedeanOrderedFieldToEventFlow_injective
    {x y : ArchimedeanOrderedFieldUp} :
    archimedeanOrderedFieldToEventFlow x =
      archimedeanOrderedFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanOrderedFieldFromEventFlow
          (archimedeanOrderedFieldToEventFlow x) =
        archimedeanOrderedFieldFromEventFlow
          (archimedeanOrderedFieldToEventFlow y) :=
    congrArg archimedeanOrderedFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (archimedeanOrderedField_round_trip x).symm
      (Eq.trans hread (archimedeanOrderedField_round_trip y)))

private theorem archimedeanOrderedFieldFields_faithful :
    ∀ x y : ArchimedeanOrderedFieldUp,
      archimedeanOrderedFieldFields x = archimedeanOrderedFieldFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk R1 A1 Q1 O1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 A2 Q2 O2 B2 H2 C2 P2 N2 =>
          cases h
          rfl

instance archimedeanOrderedFieldBHistCarrier :
    BHistCarrier ArchimedeanOrderedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanOrderedFieldToEventFlow
  fromEventFlow := archimedeanOrderedFieldFromEventFlow

instance archimedeanOrderedFieldChapterTasteGate :
    ChapterTasteGate ArchimedeanOrderedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      archimedeanOrderedFieldFromEventFlow
        (archimedeanOrderedFieldToEventFlow x) = some x
    exact archimedeanOrderedField_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (archimedeanOrderedFieldToEventFlow_injective heq)

instance archimedeanOrderedFieldFieldFaithful :
    FieldFaithful ArchimedeanOrderedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := archimedeanOrderedFieldFields
  field_faithful := archimedeanOrderedFieldFields_faithful

instance archimedeanOrderedFieldNontrivial :
    Nontrivial ArchimedeanOrderedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ArchimedeanOrderedFieldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ArchimedeanOrderedFieldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ArchimedeanOrderedFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem ArchimedeanOrderedFieldTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      archimedeanOrderedFieldDecodeBHist
        (archimedeanOrderedFieldEncodeBHist h) = h) ∧
      (∀ x : ArchimedeanOrderedFieldUp,
        archimedeanOrderedFieldFromEventFlow
          (archimedeanOrderedFieldToEventFlow x) = some x) ∧
        (∀ x y : ArchimedeanOrderedFieldUp,
          archimedeanOrderedFieldToEventFlow x =
            archimedeanOrderedFieldToEventFlow y → x = y) ∧
          archimedeanOrderedFieldEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : ArchimedeanOrderedFieldUp,
              archimedeanOrderedFieldFields x =
                archimedeanOrderedFieldFields y → x = y) ∧
              (∃ x y : ArchimedeanOrderedFieldUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact archimedeanOrderedFieldDecode_encode_bhist
  · constructor
    · exact archimedeanOrderedField_round_trip
    · constructor
      · intro x y heq
        exact archimedeanOrderedFieldToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact archimedeanOrderedFieldFields_faithful
          · exact
              ⟨ArchimedeanOrderedFieldUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                ArchimedeanOrderedFieldUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                by
                  intro h
                  cases h⟩

theorem ArchimedeanOrderedFieldRealAlgOrderHandoff [AskSetup] [PackageSetup]
    {R A Q O B H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (hAlg : Cont R A C)
    (hArch : Cont R O C)
    (hRat : Cont Q B H)
    (hprov : PkgSig bundle P pkg)
    (hname : PkgSig bundle N pkg) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧ Cont R A C ∧ Cont R O C ∧ Cont Q B H ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        (fun row : BHist => hsame row N ∧ Cont R A C ∧ Cont R O C)
        (fun row : BHist =>
          hsame row N ∧ Cont Q B H ∧ PkgSig bundle P pkg ∧
            PkgSig bundle N pkg)
        hsame ∧
      archimedeanOrderedFieldFields (ArchimedeanOrderedFieldUp.mk R A Q O B H C P N) =
        [R, A, Q, O, B, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧ Cont R A C ∧ Cont R O C ∧ Cont Q B H ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        (fun row : BHist => hsame row N ∧ Cont R A C ∧ Cont R O C)
        (fun row : BHist =>
          hsame row N ∧ Cont Q B H ∧ PkgSig bundle P pkg ∧
            PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro N ⟨hsame_refl N, hAlg, hArch, hRat, hprov, hname⟩
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
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            source.right.left, source.right.right.left, source.right.right.right.left,
            source.right.right.right.right.left,
            source.right.right.right.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, source.right.left, source.right.right.left⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, source.right.right.right.left,
          source.right.right.right.right.left,
          source.right.right.right.right.right⟩
  }
  exact And.intro cert rfl

end BEDC.Derived.ArchimedeanOrderedFieldUp
