import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FinitePrefixAutomatonUp : Type where
  | mk (Q q0 A T W R E H C P N : BHist) : FinitePrefixAutomatonUp
  deriving DecidableEq

def finitePrefixAutomatonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finitePrefixAutomatonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finitePrefixAutomatonEncodeBHist h

def finitePrefixAutomatonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finitePrefixAutomatonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finitePrefixAutomatonDecodeBHist tail)

private theorem finitePrefixAutomatonDecode_encode_bhist :
    ∀ h : BHist, finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finitePrefixAutomatonToEventFlow : FinitePrefixAutomatonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N =>
      [[BMark.b0],
        finitePrefixAutomatonEncodeBHist Q,
        [BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist q0,
        [BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finitePrefixAutomatonEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist N]

def finitePrefixAutomatonFromEventFlow : EventFlow → Option FinitePrefixAutomatonUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tagQ :: Q :: _tagQ0 :: q0 :: _tagA :: A :: _tagT :: T :: _tagW :: W ::
      _tagR :: R :: _tagE :: E :: _tagH :: H :: _tagC :: C :: _tagP :: P ::
      _tagN :: N :: [] =>
      some
        (FinitePrefixAutomatonUp.mk
          (finitePrefixAutomatonDecodeBHist Q)
          (finitePrefixAutomatonDecodeBHist q0)
          (finitePrefixAutomatonDecodeBHist A)
          (finitePrefixAutomatonDecodeBHist T)
          (finitePrefixAutomatonDecodeBHist W)
          (finitePrefixAutomatonDecodeBHist R)
          (finitePrefixAutomatonDecodeBHist E)
          (finitePrefixAutomatonDecodeBHist H)
          (finitePrefixAutomatonDecodeBHist C)
          (finitePrefixAutomatonDecodeBHist P)
          (finitePrefixAutomatonDecodeBHist N))
  | _ => none

private theorem finitePrefixAutomaton_round_trip :
    ∀ x : FinitePrefixAutomatonUp,
      finitePrefixAutomatonFromEventFlow (finitePrefixAutomatonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q q0 A T W R E H C P N =>
      change
        some
          (FinitePrefixAutomatonUp.mk
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist Q))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist q0))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist A))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist T))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist W))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist R))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist E))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist H))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist C))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist P))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist N))) =
          some (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)
      rw [finitePrefixAutomatonDecode_encode_bhist Q, finitePrefixAutomatonDecode_encode_bhist q0,
        finitePrefixAutomatonDecode_encode_bhist A, finitePrefixAutomatonDecode_encode_bhist T,
        finitePrefixAutomatonDecode_encode_bhist W, finitePrefixAutomatonDecode_encode_bhist R,
        finitePrefixAutomatonDecode_encode_bhist E, finitePrefixAutomatonDecode_encode_bhist H,
        finitePrefixAutomatonDecode_encode_bhist C, finitePrefixAutomatonDecode_encode_bhist P,
        finitePrefixAutomatonDecode_encode_bhist N]

private theorem finitePrefixAutomatonToEventFlow_injective
    {x y : FinitePrefixAutomatonUp} :
    finitePrefixAutomatonToEventFlow x = finitePrefixAutomatonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finitePrefixAutomatonFromEventFlow (finitePrefixAutomatonToEventFlow x) =
        finitePrefixAutomatonFromEventFlow (finitePrefixAutomatonToEventFlow y) :=
    congrArg finitePrefixAutomatonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finitePrefixAutomaton_round_trip x).symm
      (Eq.trans hread (finitePrefixAutomaton_round_trip y)))

private def finitePrefixAutomatonFields : FinitePrefixAutomatonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N => [Q, q0, A, T, W, R, E, H, C, P, N]

private theorem finitePrefixAutomaton_fields_faithful :
    ∀ x y : FinitePrefixAutomatonUp,
      finitePrefixAutomatonFields x = finitePrefixAutomatonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 q01 A1 T1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 q02 A2 T2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finitePrefixAutomatonBHistCarrier : BHistCarrier FinitePrefixAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finitePrefixAutomatonToEventFlow
  fromEventFlow := finitePrefixAutomatonFromEventFlow

instance finitePrefixAutomatonChapterTasteGate : ChapterTasteGate FinitePrefixAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finitePrefixAutomatonFromEventFlow (finitePrefixAutomatonToEventFlow x) = some x
    exact finitePrefixAutomaton_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finitePrefixAutomatonToEventFlow_injective heq)

instance finitePrefixAutomatonFieldFaithful : FieldFaithful FinitePrefixAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finitePrefixAutomatonFields
  field_faithful := finitePrefixAutomaton_fields_faithful

instance finitePrefixAutomatonNontrivial : Nontrivial FinitePrefixAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FinitePrefixAutomatonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FinitePrefixAutomatonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FinitePrefixAutomatonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist h) = h) ∧
      (∀ x y : FinitePrefixAutomatonUp,
        finitePrefixAutomatonFields x = finitePrefixAutomatonFields y → x = y) ∧
      finitePrefixAutomatonEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      finitePrefixAutomatonEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      (∀ x y : FinitePrefixAutomatonUp,
        x = y → finitePrefixAutomatonToEventFlow x = finitePrefixAutomatonToEventFlow y) ∧
      (∃ x y : FinitePrefixAutomatonUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact finitePrefixAutomatonDecode_encode_bhist
  constructor
  · exact finitePrefixAutomaton_fields_faithful
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro x y hxy
    cases hxy
    rfl
  · exact
      ⟨FinitePrefixAutomatonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        FinitePrefixAutomatonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩

theorem FinitePrefixAutomatonNameCertObligationSurface (F : FinitePrefixAutomatonUp) :
    SemanticNameCert
      (fun row : BHist =>
        ∃ Q q0 A T W R E H C P N : BHist,
          F = FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N ∧ hsame row H)
      (fun row : BHist =>
        ∃ Q q0 A T W R E H C P N : BHist,
          F = FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N ∧ hsame row H)
      (fun row : BHist =>
        ∃ Q q0 A T W R E H C P N : BHist,
          F = FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N ∧ hsame row H)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases F with
  | mk Q q0 A T W R E H C P N =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro H
              ⟨Q, q0, A, T, W, R, E, H, C, P, N, rfl, hsame_refl H⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other same
            exact hsame_symm same
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row other same source
            have sameRow : hsame row H := by
              cases source with
              | intro Q' source =>
                  cases source with
                  | intro q0' source =>
                      cases source with
                      | intro A' source =>
                          cases source with
                          | intro T' source =>
                              cases source with
                              | intro W' source =>
                                  cases source with
                                  | intro R' source =>
                                      cases source with
                                      | intro E' source =>
                                          cases source with
                                          | intro H' source =>
                                              cases source with
                                              | intro C' source =>
                                                  cases source with
                                                  | intro P' source =>
                                                      cases source with
                                                      | intro N' source =>
                                                          cases source.left
                                                          exact source.right
            exact
              ⟨Q, q0, A, T, W, R, E, H, C, P, N, rfl,
                hsame_trans (hsame_symm same) sameRow⟩
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

def FinitePrefixAutomatonCarrier [AskSetup] [PackageSetup]
    (Q q0 A T W R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  UnaryHistory Q ∧ UnaryHistory q0 ∧ UnaryHistory A ∧ UnaryHistory T ∧
    UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ hsame Q T ∧
        hsame q0 W ∧ hsame A R ∧ hsame H E ∧ hsame C T ∧ hsame P W ∧
          hsame N R ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem FinitePrefixAutomatonObligationWindow [AskSetup] [PackageSetup]
    {Q q0 A T W R E H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FinitePrefixAutomatonCarrier Q q0 A T W R E H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          (hsame row Q ∨ hsame row q0 ∨ hsame row A ∨ hsame row T ∨
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N) ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row T ∨ hsame row W ∨ hsame row R ∨ hsame row E)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨unaryQ, unaryQ0, unaryA, unaryT, unaryW, unaryR, unaryE, unaryH,
    unaryC, unaryP, unaryN, sameQT, sameQ0W, sameAR, sameHE, sameCT, samePW,
    sameNR, pkgP, pkgN⟩ := carrier
  have sourceAtT :
      (hsame T Q ∨ hsame T q0 ∨ hsame T A ∨ hsame T T ∨ hsame T W ∨
        hsame T R ∨ hsame T E ∨ hsame T H ∨ hsame T C ∨ hsame T P ∨
          hsame T N) ∧ UnaryHistory T :=
    ⟨Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl T)))), unaryT⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro T sourceAtT
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
        intro row other sameRows source
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        cases source.left with
        | inl sameQ =>
            exact ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameQ), otherUnary⟩
        | inr sourceRest =>
            cases sourceRest with
            | inl sameQ0 =>
                exact ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameQ0)),
                  otherUnary⟩
            | inr sourceRest =>
                cases sourceRest with
                | inl sameA =>
                    exact
                      ⟨Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameA))),
                        otherUnary⟩
                | inr sourceRest =>
                    cases sourceRest with
                    | inl sameT =>
                        exact
                          ⟨Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameT)))),
                            otherUnary⟩
                    | inr sourceRest =>
                        cases sourceRest with
                        | inl sameW =>
                            exact
                              ⟨Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameW))))),
                                otherUnary⟩
                        | inr sourceRest =>
                            cases sourceRest with
                            | inl sameR =>
                                exact
                                  ⟨Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameR)))))),
                                    otherUnary⟩
                            | inr sourceRest =>
                                cases sourceRest with
                                | inl sameE =>
                                    exact
                                      ⟨Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameE))))))),
                                        otherUnary⟩
                                | inr sourceRest =>
                                    cases sourceRest with
                                    | inl sameH =>
                                        exact
                                          ⟨Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans (hsame_symm sameRows)
                                                            sameH)))))))),
                                            otherUnary⟩
                                    | inr sourceRest =>
                                        cases sourceRest with
                                        | inl sameC =>
                                            exact
                                              ⟨Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inl
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameC))))))))),
                                                otherUnary⟩
                                        | inr sourceRest =>
                                            cases sourceRest with
                                            | inl sameP =>
                                                exact
                                                  ⟨Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (Or.inr
                                                                    (Or.inl
                                                                      (hsame_trans
                                                                        (hsame_symm sameRows)
                                                                        sameP)))))))))),
                                                    otherUnary⟩
                                            | inr sameN =>
                                                exact
                                                  ⟨Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (Or.inr
                                                                    (Or.inr
                                                                      (hsame_trans
                                                                        (hsame_symm sameRows)
                                                                        sameN)))))))))),
                                                    otherUnary⟩
    }
    pattern_sound := by
      intro row source
      cases source.left with
      | inl sameQ =>
          exact Or.inl (hsame_trans sameQ sameQT)
      | inr sourceRest =>
          cases sourceRest with
          | inl sameQ0 =>
              exact Or.inr (Or.inl (hsame_trans sameQ0 sameQ0W))
          | inr sourceRest =>
              cases sourceRest with
              | inl sameA =>
                  exact Or.inr (Or.inr (Or.inl (hsame_trans sameA sameAR)))
              | inr sourceRest =>
                  cases sourceRest with
                  | inl sameT =>
                      exact Or.inl sameT
                  | inr sourceRest =>
                      cases sourceRest with
                      | inl sameW =>
                          exact Or.inr (Or.inl sameW)
                      | inr sourceRest =>
                          cases sourceRest with
                          | inl sameR =>
                              exact Or.inr (Or.inr (Or.inl sameR))
                          | inr sourceRest =>
                              cases sourceRest with
                              | inl sameE =>
                                  exact Or.inr (Or.inr (Or.inr sameE))
                              | inr sourceRest =>
                                  cases sourceRest with
                                  | inl sameH =>
                                      exact Or.inr (Or.inr (Or.inr (hsame_trans sameH sameHE)))
                                  | inr sourceRest =>
                                      cases sourceRest with
                                      | inl sameC =>
                                          exact Or.inl (hsame_trans sameC sameCT)
                                      | inr sourceRest =>
                                          cases sourceRest with
                                          | inl sameP =>
                                              exact Or.inr (Or.inl (hsame_trans sameP samePW))
                                          | inr sameN =>
                                              exact Or.inr (Or.inr (Or.inl (hsame_trans sameN sameNR)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgP, pkgN⟩
  }

end BEDC.Derived.FinitePrefixAutomatonUp
