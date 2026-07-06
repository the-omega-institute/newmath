import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FreeWillInscriptionCommitmentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FreeWillInscriptionCommitmentUp : Type where
  | mk :
      (priorBoundary inscriptionEvent gapProvenance classifierTransport nonReduction transports
        routes package nameCert : BHist) →
      FreeWillInscriptionCommitmentUp
  deriving DecidableEq

def freeWillInscriptionCommitmentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: freeWillInscriptionCommitmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: freeWillInscriptionCommitmentEncodeBHist h

def freeWillInscriptionCommitmentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (freeWillInscriptionCommitmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (freeWillInscriptionCommitmentDecodeBHist tail)

private theorem freeWillInscriptionCommitmentDecode_encode_bhist :
    ∀ h : BHist,
      freeWillInscriptionCommitmentDecodeBHist
        (freeWillInscriptionCommitmentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def freeWillInscriptionCommitmentToEventFlow :
    FreeWillInscriptionCommitmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FreeWillInscriptionCommitmentUp.mk priorBoundary inscriptionEvent gapProvenance
      classifierTransport nonReduction transports routes package nameCert =>
      [[BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist priorBoundary,
        [BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist inscriptionEvent,
        [BMark.b1, BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist gapProvenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist classifierTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist nonReduction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist package,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist nameCert]

def freeWillInscriptionCommitmentFromEventFlow :
    EventFlow → Option FreeWillInscriptionCommitmentUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | priorBoundary :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | inscriptionEvent :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gapProvenance :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifierTransport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nonReduction :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | package :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (FreeWillInscriptionCommitmentUp.mk
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    priorBoundary)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    inscriptionEvent)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    gapProvenance)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    classifierTransport)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    nonReduction)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    transports)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    routes)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    package)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem freeWillInscriptionCommitment_round_trip :
    ∀ x : FreeWillInscriptionCommitmentUp,
      freeWillInscriptionCommitmentFromEventFlow
        (freeWillInscriptionCommitmentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk priorBoundary inscriptionEvent gapProvenance classifierTransport nonReduction transports
      routes package nameCert =>
      change
        some
          (FreeWillInscriptionCommitmentUp.mk
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist priorBoundary))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist inscriptionEvent))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist gapProvenance))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist classifierTransport))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist nonReduction))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist transports))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist routes))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist package))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist nameCert))) =
          some
            (FreeWillInscriptionCommitmentUp.mk priorBoundary inscriptionEvent gapProvenance
              classifierTransport nonReduction transports routes package nameCert)
      rw [freeWillInscriptionCommitmentDecode_encode_bhist priorBoundary,
        freeWillInscriptionCommitmentDecode_encode_bhist inscriptionEvent,
        freeWillInscriptionCommitmentDecode_encode_bhist gapProvenance,
        freeWillInscriptionCommitmentDecode_encode_bhist classifierTransport,
        freeWillInscriptionCommitmentDecode_encode_bhist nonReduction,
        freeWillInscriptionCommitmentDecode_encode_bhist transports,
        freeWillInscriptionCommitmentDecode_encode_bhist routes,
        freeWillInscriptionCommitmentDecode_encode_bhist package,
        freeWillInscriptionCommitmentDecode_encode_bhist nameCert]

private theorem freeWillInscriptionCommitmentToEventFlow_injective
    {x y : FreeWillInscriptionCommitmentUp} :
    freeWillInscriptionCommitmentToEventFlow x =
      freeWillInscriptionCommitmentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      freeWillInscriptionCommitmentFromEventFlow
          (freeWillInscriptionCommitmentToEventFlow x) =
        freeWillInscriptionCommitmentFromEventFlow
          (freeWillInscriptionCommitmentToEventFlow y) :=
    congrArg freeWillInscriptionCommitmentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (freeWillInscriptionCommitment_round_trip x).symm
      (Eq.trans hread (freeWillInscriptionCommitment_round_trip y)))

def freeWillInscriptionCommitmentFields :
    FreeWillInscriptionCommitmentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FreeWillInscriptionCommitmentUp.mk priorBoundary inscriptionEvent gapProvenance
      classifierTransport nonReduction transports routes package nameCert =>
      [priorBoundary, inscriptionEvent, gapProvenance, classifierTransport, nonReduction,
        transports, routes, package, nameCert]

private theorem freeWillInscriptionCommitment_field_faithful :
    ∀ x y : FreeWillInscriptionCommitmentUp,
      freeWillInscriptionCommitmentFields x =
        freeWillInscriptionCommitmentFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk priorBoundary inscriptionEvent gapProvenance classifierTransport nonReduction transports
      routes package nameCert =>
      cases y with
      | mk priorBoundary' inscriptionEvent' gapProvenance' classifierTransport' nonReduction'
          transports' routes' package' nameCert' =>
          cases hfields
          rfl

instance freeWillInscriptionCommitmentBHistCarrier :
    BHistCarrier FreeWillInscriptionCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := freeWillInscriptionCommitmentToEventFlow
  fromEventFlow := freeWillInscriptionCommitmentFromEventFlow

instance freeWillInscriptionCommitmentChapterTasteGate :
    ChapterTasteGate FreeWillInscriptionCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      freeWillInscriptionCommitmentFromEventFlow
        (freeWillInscriptionCommitmentToEventFlow x) = some x
    exact freeWillInscriptionCommitment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (freeWillInscriptionCommitmentToEventFlow_injective heq)

instance freeWillInscriptionCommitmentFieldFaithful :
    FieldFaithful FreeWillInscriptionCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := freeWillInscriptionCommitmentFields
  field_faithful := freeWillInscriptionCommitment_field_faithful

instance freeWillInscriptionCommitmentNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FreeWillInscriptionCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FreeWillInscriptionCommitmentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FreeWillInscriptionCommitmentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FreeWillInscriptionCommitmentTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      freeWillInscriptionCommitmentDecodeBHist
        (freeWillInscriptionCommitmentEncodeBHist h) = h) ∧
      (∀ x : FreeWillInscriptionCommitmentUp,
        freeWillInscriptionCommitmentFromEventFlow
          (freeWillInscriptionCommitmentToEventFlow x) = some x) ∧
        (∀ x y : FreeWillInscriptionCommitmentUp,
          freeWillInscriptionCommitmentToEventFlow x =
            freeWillInscriptionCommitmentToEventFlow y → x = y) ∧
          freeWillInscriptionCommitmentEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact freeWillInscriptionCommitmentDecode_encode_bhist
  · constructor
    · exact freeWillInscriptionCommitment_round_trip
    · constructor
      · intro x y heq
        exact freeWillInscriptionCommitmentToEventFlow_injective heq
      · rfl

theorem FreeWillInscriptionCommitment_namecert_obligations
    (W : FreeWillInscriptionCommitmentUp) :
    SemanticNameCert
      (fun row : BHist =>
        ∃ B I G T R H C P N : BHist,
          W = FreeWillInscriptionCommitmentUp.mk B I G T R H C P N ∧ hsame row H)
      (fun row : BHist =>
        ∃ B I G T R H C P N : BHist,
          W = FreeWillInscriptionCommitmentUp.mk B I G T R H C P N ∧ hsame row H)
      (fun row : BHist =>
        ∃ B I G T R H C P N : BHist,
          W = FreeWillInscriptionCommitmentUp.mk B I G T R H C P N ∧ hsame row H)
      hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame NameCert
  cases W with
  | mk B I G T R H C P N =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro H ⟨B, I, G, T, R, H, C, P, N, rfl, hsame_refl H⟩
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
              | intro B' source =>
                  cases source with
                  | intro I' source =>
                      cases source with
                      | intro G' source =>
                          cases source with
                          | intro T' source =>
                              cases source with
                              | intro R' source =>
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
              ⟨B, I, G, T, R, H, C, P, N, rfl, hsame_trans (hsame_symm same) sameRow⟩
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

theorem FreeWillInscriptionCommitment_inscription_event_route
    {B I G T R H C P N eventRead routeRead : BHist} :
    Cont I H eventRead →
      Cont eventRead C routeRead →
        SemanticNameCert
          (fun row : BHist => hsame row routeRead)
          (fun row : BHist =>
            hsame row B ∨ hsame row I ∨ hsame row G ∨ hsame row T ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row eventRead ∨ hsame row routeRead)
          (fun row : BHist =>
            Cont I H eventRead ∧ Cont eventRead C routeRead ∧ hsame row routeRead)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame NameCert
  intro ih eventRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro routeRead (hsame_refl routeRead)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨ih, eventRoute, source⟩
  }

theorem FreeWillInscriptionCommitment_nonescape :
    (∀ (x : FreeWillInscriptionCommitmentUp) (extra : BHist),
      freeWillInscriptionCommitmentFromEventFlow
        (List.append (freeWillInscriptionCommitmentToEventFlow x)
          [freeWillInscriptionCommitmentEncodeBHist extra]) = none) ∧
      (∀ {B I G T R H C P N eventRead routeRead : BHist},
        Cont I H eventRead →
          Cont eventRead C routeRead →
            SemanticNameCert
              (fun row : BHist => hsame row routeRead)
              (fun row : BHist =>
                hsame row B ∨ hsame row I ∨ hsame row G ∨ hsame row T ∨
                  hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row eventRead ∨ hsame row routeRead)
              (fun row : BHist =>
                Cont I H eventRead ∧ Cont eventRead C routeRead ∧ hsame row routeRead)
              hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert BMark
  constructor
  · intro x extra
    cases x with
    | mk priorBoundary inscriptionEvent gapProvenance classifierTransport nonReduction
        transports routes package nameCert =>
        rfl
  · intro B I G T R H C P N eventRead routeRead ih eventRoute
    exact {
      core := {
        carrier_inhabited := Exists.intro routeRead (hsame_refl routeRead)
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
          exact hsame_trans (hsame_symm sameRows) source
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr source)))))))))
      ledger_sound := by
        intro _row source
        exact ⟨ih, eventRoute, source⟩
    }

def FreeWillInscriptionCommitmentCarrier [AskSetup] [PackageSetup]
    (B I G T R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory N ∧ Cont B I G ∧ Cont T R H ∧ Cont H C N ∧ PkgSig bundle P pkg

theorem FreeWillInscriptionCommitment_obligation_closure [AskSetup] [PackageSetup]
    {B I G T R H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeWillInscriptionCommitmentCarrier B I G T R H C P N bundle pkg →
      SemanticNameCert (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row B ∨ hsame row I ∨ hsame row G ∨ hsame row T ∨ hsame row R ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg) hsame ∧
        Cont B I G ∧ Cont T R H ∧ Cont H C N := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨nUnary, routeBIG, routeTRH, routeHCN, pPkg⟩ := carrier
  have cert :
      SemanticNameCert (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row B ∨ hsame row I ∨ hsame row G ∨ hsame row T ∨ hsame row R ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg) hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pPkg⟩
  }
  exact ⟨cert, routeBIG, routeTRH, routeHCN⟩

theorem FreeWillInscriptionCommitment_obligation_closure_nonescape_consumer
    [AskSetup] [PackageSetup]
    {B I G T R H C P N eventRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (W : FreeWillInscriptionCommitmentUp) :
    FreeWillInscriptionCommitmentCarrier B I G T R H C P N bundle pkg →
      Cont I H eventRead →
        Cont eventRead C routeRead →
          (∀ extra : BHist,
            freeWillInscriptionCommitmentFromEventFlow
              (List.append (freeWillInscriptionCommitmentToEventFlow W)
                [freeWillInscriptionCommitmentEncodeBHist extra]) = none) ∧
            SemanticNameCert
              (fun row : BHist => hsame row routeRead)
              (fun row : BHist =>
                hsame row B ∨ hsame row I ∨ hsame row G ∨ hsame row T ∨
                  hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row eventRead ∨ hsame row routeRead)
              (fun row : BHist =>
                Cont I H eventRead ∧ Cont eventRead C routeRead ∧ hsame row routeRead)
              hsame ∧
              SemanticNameCert (fun row : BHist => hsame row N ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row B ∨ hsame row I ∨ hsame row G ∨ hsame row T ∨
                    hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg) hsame ∧
                Cont B I G ∧ Cont T R H ∧ Cont H C N := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert UnaryHistory
  intro carrier eventRoute routeContinuation
  have nonescape := FreeWillInscriptionCommitment_nonescape
  have appendBlocked :
      ∀ extra : BHist,
        freeWillInscriptionCommitmentFromEventFlow
          (List.append (freeWillInscriptionCommitmentToEventFlow W)
            [freeWillInscriptionCommitmentEncodeBHist extra]) = none :=
    nonescape.left W
  have routeCert :
      SemanticNameCert
        (fun row : BHist => hsame row routeRead)
        (fun row : BHist =>
          hsame row B ∨ hsame row I ∨ hsame row G ∨ hsame row T ∨
            hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row eventRead ∨ hsame row routeRead)
        (fun row : BHist =>
          Cont I H eventRead ∧ Cont eventRead C routeRead ∧ hsame row routeRead)
        hsame :=
    nonescape.right (B := B) (I := I) (G := G) (T := T) (R := R) (H := H)
      (C := C) (P := P) (N := N) eventRoute routeContinuation
  have closure :=
    FreeWillInscriptionCommitment_obligation_closure
      (B := B) (I := I) (G := G) (T := T) (R := R) (H := H) (C := C)
      (P := P) (N := N) (bundle := bundle) (pkg := pkg) carrier
  exact
    ⟨appendBlocked, routeCert, closure.left, closure.right.left, closure.right.right.left,
      closure.right.right.right⟩

end BEDC.Derived.FreeWillInscriptionCommitmentUp
