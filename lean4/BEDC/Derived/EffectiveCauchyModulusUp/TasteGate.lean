import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveCauchyModulusUp

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

inductive EffectiveCauchyModulusUp : Type where
  | mk (S D M T W Q E H C P N : BHist) : EffectiveCauchyModulusUp
  deriving DecidableEq

def effectiveCauchyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveCauchyModulusEncodeBHist h

def effectiveCauchyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveCauchyModulusDecodeBHist tail)

private theorem effectiveCauchyModulusDecode_encode :
    ∀ h : BHist,
      effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveCauchyModulusFields : EffectiveCauchyModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveCauchyModulusUp.mk S D M T W Q E H C P N => [S, D, M, T, W, Q, E, H, C, P, N]

def effectiveCauchyModulusToEventFlow : EffectiveCauchyModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (effectiveCauchyModulusFields x).map effectiveCauchyModulusEncodeBHist

def effectiveCauchyModulusFromEventFlow : EventFlow → Option EffectiveCauchyModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (EffectiveCauchyModulusUp.mk
                                                      (effectiveCauchyModulusDecodeBHist S)
                                                      (effectiveCauchyModulusDecodeBHist D)
                                                      (effectiveCauchyModulusDecodeBHist M)
                                                      (effectiveCauchyModulusDecodeBHist T)
                                                      (effectiveCauchyModulusDecodeBHist W)
                                                      (effectiveCauchyModulusDecodeBHist Q)
                                                      (effectiveCauchyModulusDecodeBHist E)
                                                      (effectiveCauchyModulusDecodeBHist H)
                                                      (effectiveCauchyModulusDecodeBHist C)
                                                      (effectiveCauchyModulusDecodeBHist P)
                                                      (effectiveCauchyModulusDecodeBHist N))
                                              | _ :: _ => none

private theorem effectiveCauchyModulus_round_trip :
    ∀ x : EffectiveCauchyModulusUp,
      effectiveCauchyModulusFromEventFlow (effectiveCauchyModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D M T W Q E H C P N =>
      change
        some
          (EffectiveCauchyModulusUp.mk
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist S))
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist D))
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist M))
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist T))
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist W))
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist Q))
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist E))
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist H))
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist C))
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist P))
            (effectiveCauchyModulusDecodeBHist (effectiveCauchyModulusEncodeBHist N))) =
          some (EffectiveCauchyModulusUp.mk S D M T W Q E H C P N)
      rw [effectiveCauchyModulusDecode_encode S, effectiveCauchyModulusDecode_encode D,
        effectiveCauchyModulusDecode_encode M, effectiveCauchyModulusDecode_encode T,
        effectiveCauchyModulusDecode_encode W, effectiveCauchyModulusDecode_encode Q,
        effectiveCauchyModulusDecode_encode E, effectiveCauchyModulusDecode_encode H,
        effectiveCauchyModulusDecode_encode C, effectiveCauchyModulusDecode_encode P,
        effectiveCauchyModulusDecode_encode N]

private theorem effectiveCauchyModulusToEventFlow_injective
    {x y : EffectiveCauchyModulusUp} :
    effectiveCauchyModulusToEventFlow x = effectiveCauchyModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveCauchyModulusFromEventFlow (effectiveCauchyModulusToEventFlow x) =
        effectiveCauchyModulusFromEventFlow (effectiveCauchyModulusToEventFlow y) :=
    congrArg effectiveCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (effectiveCauchyModulus_round_trip x).symm
      (Eq.trans hread (effectiveCauchyModulus_round_trip y)))

private theorem effectiveCauchyModulus_fields_faithful :
    ∀ x y : EffectiveCauchyModulusUp,
      effectiveCauchyModulusFields x = effectiveCauchyModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 D1 M1 T1 W1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 D2 M2 T2 W2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance effectiveCauchyModulusBHistCarrier : BHistCarrier EffectiveCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveCauchyModulusToEventFlow
  fromEventFlow := effectiveCauchyModulusFromEventFlow

instance effectiveCauchyModulusChapterTasteGate :
    ChapterTasteGate EffectiveCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveCauchyModulusFromEventFlow (effectiveCauchyModulusToEventFlow x) = some x
    exact effectiveCauchyModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveCauchyModulusToEventFlow_injective heq)

instance effectiveCauchyModulusFieldFaithful :
    FieldFaithful EffectiveCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := effectiveCauchyModulusFields
  field_faithful := effectiveCauchyModulus_fields_faithful

instance effectiveCauchyModulusNontrivial : Nontrivial EffectiveCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EffectiveCauchyModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EffectiveCauchyModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def EffectiveCauchyModulusCarrier [AskSetup] [PackageSetup]
    (S D M T W Q E H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory T ∧
    UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem EffectiveCauchyModulusCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S D M T W Q E H C P N scheduleRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EffectiveCauchyModulusCarrier S D M T W Q E H C P N bundle pkg ->
      Cont S M scheduleRead ->
        Cont scheduleRead E sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row D ∨ hsame row M ∨ hsame row T ∨
                    hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory scheduleRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier scheduleRoute sealRoute sealPkg
  obtain ⟨sUnary, _dUnary, mUnary, _tUnary, _wUnary, _qUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, provenancePkg⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed sUnary mUnary scheduleRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed scheduleUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row D ∨ hsame row M ∨ hsame row T ∨
              hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, scheduleUnary, sealUnary⟩

end BEDC.Derived.EffectiveCauchyModulusUp
