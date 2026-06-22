import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WassersteinUp

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

inductive WassersteinUp : Type where
  | mk (M K mu nu Gamma A B C H R P N : BHist) : WassersteinUp
  deriving DecidableEq

def wassersteinEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: wassersteinEncodeBHist h
  | BHist.e1 h => BMark.b1 :: wassersteinEncodeBHist h

def wassersteinDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (wassersteinDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (wassersteinDecodeBHist tail)

private theorem WassersteinTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, wassersteinDecodeBHist (wassersteinEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def wassersteinFields : WassersteinUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WassersteinUp.mk M K mu nu Gamma A B C H R P N => [M, K, mu, nu, Gamma, A, B, C, H, R, P, N]

def wassersteinToEventFlow : WassersteinUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (wassersteinFields x).map wassersteinEncodeBHist

private def wassersteinEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => wassersteinEventAt index rest

def wassersteinFromEventFlow (ef : EventFlow) : Option WassersteinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WassersteinUp.mk
      (wassersteinDecodeBHist (wassersteinEventAt 0 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 1 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 2 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 3 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 4 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 5 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 6 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 7 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 8 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 9 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 10 ef))
      (wassersteinDecodeBHist (wassersteinEventAt 11 ef)))

private theorem WassersteinTasteGate_single_carrier_alignment_round_trip
    (x : WassersteinUp) :
    wassersteinFromEventFlow (wassersteinToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M K mu nu Gamma A B C H R P N =>
      change
        some
          (WassersteinUp.mk
            (wassersteinDecodeBHist (wassersteinEncodeBHist M))
            (wassersteinDecodeBHist (wassersteinEncodeBHist K))
            (wassersteinDecodeBHist (wassersteinEncodeBHist mu))
            (wassersteinDecodeBHist (wassersteinEncodeBHist nu))
            (wassersteinDecodeBHist (wassersteinEncodeBHist Gamma))
            (wassersteinDecodeBHist (wassersteinEncodeBHist A))
            (wassersteinDecodeBHist (wassersteinEncodeBHist B))
            (wassersteinDecodeBHist (wassersteinEncodeBHist C))
            (wassersteinDecodeBHist (wassersteinEncodeBHist H))
            (wassersteinDecodeBHist (wassersteinEncodeBHist R))
            (wassersteinDecodeBHist (wassersteinEncodeBHist P))
            (wassersteinDecodeBHist (wassersteinEncodeBHist N))) =
          some (WassersteinUp.mk M K mu nu Gamma A B C H R P N)
      rw [WassersteinTasteGate_single_carrier_alignment_decode_encode M,
        WassersteinTasteGate_single_carrier_alignment_decode_encode K,
        WassersteinTasteGate_single_carrier_alignment_decode_encode mu,
        WassersteinTasteGate_single_carrier_alignment_decode_encode nu,
        WassersteinTasteGate_single_carrier_alignment_decode_encode Gamma,
        WassersteinTasteGate_single_carrier_alignment_decode_encode A,
        WassersteinTasteGate_single_carrier_alignment_decode_encode B,
        WassersteinTasteGate_single_carrier_alignment_decode_encode C,
        WassersteinTasteGate_single_carrier_alignment_decode_encode H,
        WassersteinTasteGate_single_carrier_alignment_decode_encode R,
        WassersteinTasteGate_single_carrier_alignment_decode_encode P,
        WassersteinTasteGate_single_carrier_alignment_decode_encode N]

private theorem WassersteinTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : WassersteinUp} :
    wassersteinToEventFlow x = wassersteinToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      wassersteinFromEventFlow (wassersteinToEventFlow x) =
        wassersteinFromEventFlow (wassersteinToEventFlow y) :=
    congrArg wassersteinFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (WassersteinTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WassersteinTasteGate_single_carrier_alignment_round_trip y)))

private theorem WassersteinTasteGate_single_carrier_alignment_fields :
    ∀ x y : WassersteinUp, wassersteinFields x = wassersteinFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ K₁ mu₁ nu₁ Gamma₁ A₁ B₁ C₁ H₁ R₁ P₁ N₁ =>
      cases y with
      | mk M₂ K₂ mu₂ nu₂ Gamma₂ A₂ B₂ C₂ H₂ R₂ P₂ N₂ =>
          cases hfields
          rfl

instance wassersteinBHistCarrier : BHistCarrier WassersteinUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := wassersteinToEventFlow
  fromEventFlow := wassersteinFromEventFlow

instance wassersteinChapterTasteGate : ChapterTasteGate WassersteinUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change wassersteinFromEventFlow (wassersteinToEventFlow x) = some x
    exact WassersteinTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WassersteinTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance wassersteinFieldFaithful : FieldFaithful WassersteinUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := wassersteinFields
  field_faithful := WassersteinTasteGate_single_carrier_alignment_fields

instance wassersteinNontrivial : Nontrivial WassersteinUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WassersteinUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WassersteinUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def WassersteinTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate WassersteinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  wassersteinChapterTasteGate

def WassersteinTransportPlanCarrier [AskSetup] [PackageSetup]
    (M K mu nu Gamma A B C H R P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory M ∧ UnaryHistory K ∧ UnaryHistory mu ∧ UnaryHistory nu ∧
    UnaryHistory Gamma ∧ UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧
      UnaryHistory H ∧ UnaryHistory R ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg

theorem WassersteinCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M K mu nu Gamma A B C H R P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WassersteinTransportPlanCarrier M K mu nu Gamma A B C H R P N bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row Gamma ∨ hsame row A ∨ hsame row B ∨ hsame row C ∨ hsame row N)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
          hsame ∧
        PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨_mUnary, _kUnary, _muUnary, _nuUnary, gammaUnary, aUnary, bUnary, cUnary,
    _hUnary, _rUnary, _pUnary, nUnary, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row Gamma ∨ hsame row A ∨ hsame row B ∨ hsame row C ∨ hsame row N)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro Gamma (Or.inl (hsame_refl Gamma))
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
        | inl sameGamma =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameGamma)
        | inr rest =>
            cases rest with
            | inl sameA =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameA))
            | inr rest =>
                cases rest with
                | inl sameB =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameB)))
                | inr rest =>
                    cases rest with
                    | inl sameC =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameC))))
                    | inr sameN =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (hsame_trans (hsame_symm sameRows) sameN))))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameGamma =>
          exact unary_transport gammaUnary (hsame_symm sameGamma)
      | inr rest =>
          cases rest with
          | inl sameA =>
              exact unary_transport aUnary (hsame_symm sameA)
          | inr rest =>
              cases rest with
              | inl sameB =>
                  exact unary_transport bUnary (hsame_symm sameB)
              | inr rest =>
                  cases rest with
                  | inl sameC =>
                      exact unary_transport cUnary (hsame_symm sameC)
                  | inr sameN =>
                      exact unary_transport nUnary (hsame_symm sameN)
    ledger_sound := by
      intro _row _source
      exact Or.inl provenancePkg
  }
  exact ⟨cert, provenancePkg⟩

end BEDC.Derived.WassersteinUp
