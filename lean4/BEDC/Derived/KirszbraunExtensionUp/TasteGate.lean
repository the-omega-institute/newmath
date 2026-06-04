import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KirszbraunExtensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KirszbraunExtensionUp : Type where
  | mk (X A L Y V B F R H C P N : BHist) : KirszbraunExtensionUp
  deriving DecidableEq

def kirszbraunExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kirszbraunExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kirszbraunExtensionEncodeBHist h

def kirszbraunExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kirszbraunExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kirszbraunExtensionDecodeBHist tail)

private theorem kirszbraunExtension_decode_encode :
    ∀ h : BHist, kirszbraunExtensionDecodeBHist
      (kirszbraunExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kirszbraunExtensionFields : KirszbraunExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KirszbraunExtensionUp.mk X A L Y V B F R H C P N =>
      [X, A, L, Y, V, B, F, R, H, C, P, N]

def kirszbraunExtensionToEventFlow : KirszbraunExtensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kirszbraunExtensionFields x).map kirszbraunExtensionEncodeBHist

private def kirszbraunExtensionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => kirszbraunExtensionRawAt n rest

private def kirszbraunExtensionLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => kirszbraunExtensionLengthEq n rest

def kirszbraunExtensionFromEventFlow : EventFlow → Option KirszbraunExtensionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match kirszbraunExtensionLengthEq 12 flow with
      | true =>
          some
            (KirszbraunExtensionUp.mk
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 0 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 1 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 2 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 3 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 4 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 5 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 6 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 7 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 8 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 9 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 10 flow))
              (kirszbraunExtensionDecodeBHist (kirszbraunExtensionRawAt 11 flow)))
      | false => none

private theorem kirszbraunExtension_round_trip :
    ∀ x : KirszbraunExtensionUp,
      kirszbraunExtensionFromEventFlow (kirszbraunExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A L Y V B F R H C P N =>
      change
        some
          (KirszbraunExtensionUp.mk
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist X))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist A))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist L))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist Y))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist V))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist B))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist F))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist R))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist H))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist C))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist P))
            (kirszbraunExtensionDecodeBHist (kirszbraunExtensionEncodeBHist N))) =
          some (KirszbraunExtensionUp.mk X A L Y V B F R H C P N)
      rw [kirszbraunExtension_decode_encode X, kirszbraunExtension_decode_encode A,
        kirszbraunExtension_decode_encode L, kirszbraunExtension_decode_encode Y,
        kirszbraunExtension_decode_encode V, kirszbraunExtension_decode_encode B,
        kirszbraunExtension_decode_encode F, kirszbraunExtension_decode_encode R,
        kirszbraunExtension_decode_encode H, kirszbraunExtension_decode_encode C,
        kirszbraunExtension_decode_encode P, kirszbraunExtension_decode_encode N]

private theorem kirszbraunExtensionToEventFlow_injective {x y : KirszbraunExtensionUp} :
    kirszbraunExtensionToEventFlow x = kirszbraunExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kirszbraunExtensionFromEventFlow (kirszbraunExtensionToEventFlow x) =
        kirszbraunExtensionFromEventFlow (kirszbraunExtensionToEventFlow y) :=
    congrArg kirszbraunExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kirszbraunExtension_round_trip x).symm
      (Eq.trans hread (kirszbraunExtension_round_trip y)))

private theorem kirszbraunExtension_fields_faithful :
    ∀ x y : KirszbraunExtensionUp, kirszbraunExtensionFields x =
      kirszbraunExtensionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 A1 L1 Y1 V1 B1 F1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 A2 L2 Y2 V2 B2 F2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance kirszbraunExtensionBHistCarrier : BHistCarrier KirszbraunExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kirszbraunExtensionToEventFlow
  fromEventFlow := kirszbraunExtensionFromEventFlow

instance kirszbraunExtensionChapterTasteGate : ChapterTasteGate KirszbraunExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kirszbraunExtensionFromEventFlow (kirszbraunExtensionToEventFlow x) = some x
    exact kirszbraunExtension_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kirszbraunExtensionToEventFlow_injective heq)

instance kirszbraunExtensionFieldFaithful : FieldFaithful KirszbraunExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kirszbraunExtensionFields
  field_faithful := kirszbraunExtension_fields_faithful

instance kirszbraunExtensionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial KirszbraunExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KirszbraunExtensionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      KirszbraunExtensionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KirszbraunExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kirszbraunExtensionChapterTasteGate

structure KirszbraunExtensionCarrier [AskSetup] [PackageSetup]
    (X A L Y V B F R H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop where
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  unaryX : UnaryHistory X
  unaryA : UnaryHistory A
  unaryL : UnaryHistory L
  unaryY : UnaryHistory Y
  unaryV : UnaryHistory V
  unaryB : UnaryHistory B
  unaryF : UnaryHistory F
  unaryR : UnaryHistory R
  unaryH : UnaryHistory H
  unaryC : UnaryHistory C
  unaryP : UnaryHistory P
  unaryN : UnaryHistory N
  contXAL : Cont X A L
  contYVB : Cont Y V B
  contFRH : Cont F R H
  contHCP : Cont H C P
  pkgP : PkgSig bundle P pkg
  pkgN : PkgSig bundle N pkg

theorem KirszbraunExtension_namecert_obligations [AskSetup] [PackageSetup]
    {X A L Y V B F R H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KirszbraunExtensionCarrier X A L Y V B F R H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          KirszbraunExtensionCarrier X A L Y V B F R H C P N bundle pkg ∧
            (hsame row X ∨ hsame row A ∨ hsame row L ∨ hsame row Y ∨
              hsame row V ∨ hsame row B ∨ hsame row F ∨ hsame row R ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N))
        (fun _row : BHist =>
          Cont X A L ∧ Cont Y V B ∧ Cont F R H ∧ Cont H C P ∧
            PkgSig bundle P pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro N (And.intro carrier (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl N)))))))))))))
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left.contXAL, source.left.contYVB, source.left.contFRH,
        source.left.contHCP, source.left.pkgP⟩
    ledger_sound := by
      intro row source
      cases source.right with
      | inl hrow =>
          cases hrow
          exact ⟨source.left.unaryX, carrier.pkgN⟩
      | inr rest =>
          cases rest with
          | inl hrow =>
              cases hrow
              exact ⟨source.left.unaryA, carrier.pkgN⟩
          | inr rest =>
              cases rest with
              | inl hrow =>
                  cases hrow
                  exact ⟨source.left.unaryL, carrier.pkgN⟩
              | inr rest =>
                  cases rest with
                  | inl hrow =>
                      cases hrow
                      exact ⟨source.left.unaryY, carrier.pkgN⟩
                  | inr rest =>
                      cases rest with
                      | inl hrow =>
                          cases hrow
                          exact ⟨source.left.unaryV, carrier.pkgN⟩
                      | inr rest =>
                          cases rest with
                          | inl hrow =>
                              cases hrow
                              exact ⟨source.left.unaryB, carrier.pkgN⟩
                          | inr rest =>
                              cases rest with
                              | inl hrow =>
                                  cases hrow
                                  exact ⟨source.left.unaryF, carrier.pkgN⟩
                              | inr rest =>
                                  cases rest with
                                  | inl hrow =>
                                      cases hrow
                                      exact ⟨source.left.unaryR, carrier.pkgN⟩
                                  | inr rest =>
                                      cases rest with
                                      | inl hrow =>
                                          cases hrow
                                          exact ⟨source.left.unaryH, carrier.pkgN⟩
                                      | inr rest =>
                                          cases rest with
                                          | inl hrow =>
                                              cases hrow
                                              exact ⟨source.left.unaryC, carrier.pkgN⟩
                                          | inr rest =>
                                              cases rest with
                                              | inl hrow =>
                                                  cases hrow
                                                  exact ⟨source.left.unaryP, carrier.pkgN⟩
                                              | inr hrow =>
                                                  cases hrow
                                                  exact ⟨source.left.unaryN, carrier.pkgN⟩
  }

end BEDC.Derived.KirszbraunExtensionUp
