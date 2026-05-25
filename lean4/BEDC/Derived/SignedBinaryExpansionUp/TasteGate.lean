import BEDC.Derived.SignedBinaryExpansionUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SignedBinaryExpansionUp

abbrev SignedBinaryExpansionUp := BEDC.Derived.SignedBinaryExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def signedBinaryExpansionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: signedBinaryExpansionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: signedBinaryExpansionEncodeBHist h

def signedBinaryExpansionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (signedBinaryExpansionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (signedBinaryExpansionDecodeBHist tail)

private theorem signedBinaryExpansionDecode_encode_bhist :
    ∀ h : BHist, signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def signedBinaryExpansionFields : SignedBinaryExpansionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SignedBinaryExpansionUp.mk Q B U D W E Y R L H C P N =>
      [Q, B, U, D, W, E, Y, R, L, H, C, P, N]

def signedBinaryExpansionToEventFlow : SignedBinaryExpansionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (signedBinaryExpansionFields x).map signedBinaryExpansionEncodeBHist

def signedBinaryExpansionFromEventFlow : EventFlow → Option SignedBinaryExpansionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [Q, B, U, D, W, E, Y, R, L, H, C, P, N] =>
      some
        (SignedBinaryExpansionUp.mk
          (signedBinaryExpansionDecodeBHist Q)
          (signedBinaryExpansionDecodeBHist B)
          (signedBinaryExpansionDecodeBHist U)
          (signedBinaryExpansionDecodeBHist D)
          (signedBinaryExpansionDecodeBHist W)
          (signedBinaryExpansionDecodeBHist E)
          (signedBinaryExpansionDecodeBHist Y)
          (signedBinaryExpansionDecodeBHist R)
          (signedBinaryExpansionDecodeBHist L)
          (signedBinaryExpansionDecodeBHist H)
          (signedBinaryExpansionDecodeBHist C)
          (signedBinaryExpansionDecodeBHist P)
          (signedBinaryExpansionDecodeBHist N))
  | _ => none

private theorem signedBinaryExpansion_round_trip :
    ∀ x : SignedBinaryExpansionUp,
      signedBinaryExpansionFromEventFlow (signedBinaryExpansionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q B U D W E Y R L H C P N =>
      change
        some
          (SignedBinaryExpansionUp.mk
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist Q))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist B))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist U))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist D))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist W))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist E))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist Y))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist R))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist L))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist H))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist C))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist P))
            (signedBinaryExpansionDecodeBHist (signedBinaryExpansionEncodeBHist N))) =
          some (SignedBinaryExpansionUp.mk Q B U D W E Y R L H C P N)
      rw [signedBinaryExpansionDecode_encode_bhist Q, signedBinaryExpansionDecode_encode_bhist B,
        signedBinaryExpansionDecode_encode_bhist U, signedBinaryExpansionDecode_encode_bhist D,
        signedBinaryExpansionDecode_encode_bhist W, signedBinaryExpansionDecode_encode_bhist E,
        signedBinaryExpansionDecode_encode_bhist Y, signedBinaryExpansionDecode_encode_bhist R,
        signedBinaryExpansionDecode_encode_bhist L, signedBinaryExpansionDecode_encode_bhist H,
        signedBinaryExpansionDecode_encode_bhist C, signedBinaryExpansionDecode_encode_bhist P,
        signedBinaryExpansionDecode_encode_bhist N]

private theorem signedBinaryExpansionToEventFlow_injective
    {x y : SignedBinaryExpansionUp} :
    signedBinaryExpansionToEventFlow x = signedBinaryExpansionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      signedBinaryExpansionFromEventFlow (signedBinaryExpansionToEventFlow x) =
        signedBinaryExpansionFromEventFlow (signedBinaryExpansionToEventFlow y) :=
    congrArg signedBinaryExpansionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (signedBinaryExpansion_round_trip x).symm
      (Eq.trans hread (signedBinaryExpansion_round_trip y)))

private theorem signedBinaryExpansion_fields_faithful :
    ∀ x y : SignedBinaryExpansionUp, signedBinaryExpansionFields x = signedBinaryExpansionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 B1 U1 D1 W1 E1 Y1 R1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 B2 U2 D2 W2 E2 Y2 R2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance signedBinaryExpansionBHistCarrier : BHistCarrier SignedBinaryExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := signedBinaryExpansionToEventFlow
  fromEventFlow := signedBinaryExpansionFromEventFlow

instance signedBinaryExpansionChapterTasteGate : ChapterTasteGate SignedBinaryExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change signedBinaryExpansionFromEventFlow (signedBinaryExpansionToEventFlow x) = some x
    exact signedBinaryExpansion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (signedBinaryExpansionToEventFlow_injective heq)

instance signedBinaryExpansionFieldFaithful : FieldFaithful SignedBinaryExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := signedBinaryExpansionFields
  field_faithful := signedBinaryExpansion_fields_faithful

instance signedBinaryExpansionNontrivial : Nontrivial SignedBinaryExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SignedBinaryExpansionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SignedBinaryExpansionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SignedBinaryExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  signedBinaryExpansionChapterTasteGate

def SignedBinaryExpansionCarrier [AskSetup] [PackageSetup]
    (Q B U D W E Y R L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  UnaryHistory Q ∧ UnaryHistory B ∧ UnaryHistory U ∧ UnaryHistory D ∧
    UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory Y ∧ UnaryHistory R ∧
      UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ hsame H (append C W) ∧ PkgSig bundle P pkg

theorem SignedBinaryExpansionCarrier_real_readback_boundary [AskSetup] [PackageSetup]
    {Q B U D W E Y R L H C P N readback sealRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedBinaryExpansionCarrier Q B U D W E Y R L H C P N bundle pkg →
      Cont E Y readback →
        Cont readback R sealRead →
          Cont sealRead L terminal →
            UnaryHistory readback ∧ UnaryHistory sealRead ∧ UnaryHistory terminal ∧
              hsame H (append C W) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier enclosureRoute regularRoute terminalRoute
  obtain ⟨_qUnary, _bUnary, _uUnary, _dUnary, _wUnary, eUnary, yUnary, rUnary, lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, transportRow, provenance⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed eUnary yUnary enclosureRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary rUnary regularRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealReadUnary lUnary terminalRoute
  exact ⟨readbackUnary, sealReadUnary, terminalUnary, transportRow, provenance⟩

namespace TasteGate

def SignedBinaryExpansionCarrier (row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  ∃ Q B U D W E Y R L H C P N : BHist,
    hsame row N ∧
      Cont Q B U ∧ Cont U D W ∧ Cont W E Y ∧ Cont Y R L ∧ Cont H C P

def SignedBinaryExpansionHandoffPattern (row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  ∃ Q B U D W E Y R L H C P N : BHist,
    hsame row N ∧
      Cont Q B U ∧ Cont U D W ∧ Cont W E Y ∧ Cont Y R L ∧ Cont H C P

def SignedBinaryExpansionLedgerPolicy (row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  ∃ H C P N : BHist, hsame row N ∧ Cont H C P

def SignedBinaryExpansionClassifier (row row' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame NameCert
  hsame row row'

theorem SignedBinaryExpansion_real_readback_boundary
    {Q B U D W E Y R L H C P N readback «seal» : BHist} :
    SignedBinaryExpansionCarrier N →
      Cont Q B U →
        Cont U D W →
          Cont W E Y →
            Cont Y R L →
              hsame readback R →
                hsame «seal» L →
                  SignedBinaryExpansionHandoffPattern N ∧
                    SignedBinaryExpansionLedgerPolicy N ∧
                      SignedBinaryExpansionClassifier readback R ∧
                        SignedBinaryExpansionClassifier «seal» L := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  intro carrier _signRoute _windowRoute _enclosureRoute _realRoute sameReadback sameSeal
  obtain ⟨Q0, B0, U0, D0, W0, E0, Y0, R0, L0, H0, C0, P0, N0, sameName,
    signRoute, windowRoute, enclosureRoute, realRoute, structuralRoute⟩ := carrier
  exact
    ⟨⟨Q0, B0, U0, D0, W0, E0, Y0, R0, L0, H0, C0, P0, N0, sameName,
        signRoute, windowRoute, enclosureRoute, realRoute, structuralRoute⟩,
      ⟨H0, C0, P0, N0, sameName, structuralRoute⟩,
      sameReadback,
      sameSeal⟩

def taste_gate : ChapterTasteGate SignedBinaryExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.SignedBinaryExpansionUp.taste_gate

end TasteGate

end BEDC.Derived.SignedBinaryExpansionUp
