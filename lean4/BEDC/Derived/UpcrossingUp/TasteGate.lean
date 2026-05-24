import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UpcrossingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UpcrossingUp : Type where
  | mk (omega martingale lower upper horizon values lowerLedger upperLedger transport routes
      provenance nameCert : BHist) : UpcrossingUp
  deriving DecidableEq

def upcrossingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: upcrossingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: upcrossingEncodeBHist h

def upcrossingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (upcrossingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (upcrossingDecodeBHist tail)

private theorem upcrossingDecode_encode_bhist :
    ∀ h : BHist, upcrossingDecodeBHist (upcrossingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def upcrossingFields : UpcrossingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UpcrossingUp.mk omega martingale lower upper horizon values lowerLedger upperLedger
      transport routes provenance nameCert =>
      [omega, martingale, lower, upper, horizon, values, lowerLedger, upperLedger,
        transport, routes, provenance, nameCert]

def upcrossingToEventFlow : UpcrossingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (upcrossingFields x).map upcrossingEncodeBHist

private def upcrossingRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => upcrossingRawAt n rest

def upcrossingFromEventFlow (flow : EventFlow) : Option UpcrossingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UpcrossingUp.mk
      (upcrossingDecodeBHist (upcrossingRawAt 0 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 1 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 2 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 3 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 4 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 5 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 6 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 7 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 8 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 9 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 10 flow))
      (upcrossingDecodeBHist (upcrossingRawAt 11 flow)))

private theorem upcrossing_round_trip :
    ∀ x : UpcrossingUp, upcrossingFromEventFlow (upcrossingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk omega martingale lower upper horizon values lowerLedger upperLedger transport routes
      provenance nameCert =>
      change
        some
          (UpcrossingUp.mk
            (upcrossingDecodeBHist (upcrossingEncodeBHist omega))
            (upcrossingDecodeBHist (upcrossingEncodeBHist martingale))
            (upcrossingDecodeBHist (upcrossingEncodeBHist lower))
            (upcrossingDecodeBHist (upcrossingEncodeBHist upper))
            (upcrossingDecodeBHist (upcrossingEncodeBHist horizon))
            (upcrossingDecodeBHist (upcrossingEncodeBHist values))
            (upcrossingDecodeBHist (upcrossingEncodeBHist lowerLedger))
            (upcrossingDecodeBHist (upcrossingEncodeBHist upperLedger))
            (upcrossingDecodeBHist (upcrossingEncodeBHist transport))
            (upcrossingDecodeBHist (upcrossingEncodeBHist routes))
            (upcrossingDecodeBHist (upcrossingEncodeBHist provenance))
            (upcrossingDecodeBHist (upcrossingEncodeBHist nameCert))) =
          some
            (UpcrossingUp.mk omega martingale lower upper horizon values lowerLedger
              upperLedger transport routes provenance nameCert)
      rw [upcrossingDecode_encode_bhist omega, upcrossingDecode_encode_bhist martingale,
        upcrossingDecode_encode_bhist lower, upcrossingDecode_encode_bhist upper,
        upcrossingDecode_encode_bhist horizon, upcrossingDecode_encode_bhist values,
        upcrossingDecode_encode_bhist lowerLedger, upcrossingDecode_encode_bhist upperLedger,
        upcrossingDecode_encode_bhist transport, upcrossingDecode_encode_bhist routes,
        upcrossingDecode_encode_bhist provenance, upcrossingDecode_encode_bhist nameCert]

private theorem upcrossingToEventFlow_injective {x y : UpcrossingUp} :
    upcrossingToEventFlow x = upcrossingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      upcrossingFromEventFlow (upcrossingToEventFlow x) =
        upcrossingFromEventFlow (upcrossingToEventFlow y) :=
    congrArg upcrossingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (upcrossing_round_trip x).symm
      (Eq.trans hread (upcrossing_round_trip y)))

private theorem upcrossing_fields_faithful :
    ∀ x y : UpcrossingUp, upcrossingFields x = upcrossingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk omega₁ martingale₁ lower₁ upper₁ horizon₁ values₁ lowerLedger₁ upperLedger₁
      transport₁ routes₁ provenance₁ nameCert₁ =>
      cases y with
      | mk omega₂ martingale₂ lower₂ upper₂ horizon₂ values₂ lowerLedger₂ upperLedger₂
          transport₂ routes₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance upcrossingBHistCarrier : BHistCarrier UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := upcrossingToEventFlow
  fromEventFlow := upcrossingFromEventFlow

instance upcrossingChapterTasteGate : ChapterTasteGate UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change upcrossingFromEventFlow (upcrossingToEventFlow x) = some x
    exact upcrossing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (upcrossingToEventFlow_injective heq)

instance upcrossingFieldFaithful : FieldFaithful UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := upcrossingFields
  field_faithful := upcrossing_fields_faithful

instance upcrossingNontrivial : Nontrivial UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UpcrossingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UpcrossingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UpcrossingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  upcrossingChapterTasteGate

theorem UpcrossingTasteGate_single_carrier_alignment :
    (∀ h : BHist, upcrossingDecodeBHist (upcrossingEncodeBHist h) = h) ∧
      (∀ x : UpcrossingUp, upcrossingFromEventFlow (upcrossingToEventFlow x) = some x) ∧
        (∀ x y : UpcrossingUp, upcrossingToEventFlow x = upcrossingToEventFlow y → x = y) ∧
          upcrossingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨upcrossingDecode_encode_bhist,
      upcrossing_round_trip,
      fun _ _ heq => upcrossingToEventFlow_injective heq,
      rfl⟩

def UpcrossingCarrier [AskSetup] [PackageSetup]
    (source martingale window threshold route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory martingale ∧ UnaryHistory window ∧
    UnaryHistory threshold ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory localCert ∧ PkgSig bundle provenance pkg

theorem UpcrossingNamecertObligations [AskSetup] [PackageSetup]
    {source martingale window threshold route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UpcrossingCarrier source martingale window threshold route provenance localCert
        bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row route ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row martingale ∨ hsame row window ∨
              hsame row threshold ∨ hsame row route)
          (fun row : BHist => hsame row route ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory source ∧ UnaryHistory martingale ∧ UnaryHistory window ∧
          UnaryHistory threshold ∧ UnaryHistory route ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨sourceUnary, martingaleUnary, windowUnary, thresholdUnary, routeUnary,
    _provenanceUnary, _localCertUnary, provenancePkg⟩ := carrier
  have sourceRoute :
      (fun row : BHist => hsame row route ∧ UnaryHistory row) route := by
    exact ⟨hsame_refl route, routeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row route ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row martingale ∨ hsame row window ∨
              hsame row threshold ∨ hsame row route)
          (fun row : BHist => hsame row route ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro route sourceRoute
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
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, sourceUnary, martingaleUnary, windowUnary, thresholdUnary, routeUnary,
      provenancePkg⟩

theorem UpcrossingMartingaleRoute [AskSetup] [PackageSetup]
    {source martingale window threshold route provenance localCert routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UpcrossingCarrier source martingale window threshold route provenance localCert
        bundle pkg →
      Cont martingale window routeRead →
        PkgSig bundle routeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row martingale ∨ hsame row window ∨ hsame row routeRead)
              (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
              hsame ∧
            UnaryHistory martingale ∧ UnaryHistory window ∧ UnaryHistory routeRead ∧
              Cont martingale window routeRead ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier martingaleWindow routePkg
  obtain ⟨_sourceUnary, martingaleUnary, windowUnary, _thresholdUnary, _routeUnary,
    _provenanceUnary, _localCertUnary, _provenancePkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed martingaleUnary windowUnary martingaleWindow
  have sourceRoute :
      (fun row : BHist => hsame row routeRead ∧ UnaryHistory row) routeRead := by
    exact ⟨hsame_refl routeRead, routeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row martingale ∨ hsame row window ∨ hsame row routeRead)
          (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead sourceRoute
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
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routePkg⟩
  }
  exact ⟨cert, martingaleUnary, windowUnary, routeReadUnary, martingaleWindow, routePkg⟩

theorem Upcrossing_nonescape [AskSetup] [PackageSetup]
    {source martingale window threshold route provenance localCert routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UpcrossingCarrier source martingale window threshold route provenance localCert
        bundle pkg →
      Cont martingale window routeRead →
        PkgSig bundle routeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row route ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row martingale ∨ hsame row window ∨
                  hsame row threshold ∨ hsame row route)
              (fun row : BHist => hsame row route ∧ PkgSig bundle provenance pkg)
              hsame ∧
            SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row martingale ∨ hsame row window ∨ hsame row routeRead)
              (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
              hsame ∧
            UnaryHistory source ∧ UnaryHistory martingale ∧ UnaryHistory window ∧
              UnaryHistory threshold ∧ UnaryHistory route ∧ UnaryHistory routeRead ∧
                Cont martingale window routeRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier martingaleWindow routePkg
  obtain ⟨routeCert, sourceUnary, martingaleUnary, windowUnary, thresholdUnary,
    routeUnary, provenancePkg⟩ := UpcrossingNamecertObligations carrier
  obtain ⟨routeReadCert, _martingaleUnary, _windowUnary, routeReadUnary,
    martingaleWindowProof, routeReadPkg⟩ :=
    UpcrossingMartingaleRoute carrier martingaleWindow routePkg
  exact
    ⟨routeCert, routeReadCert, sourceUnary, martingaleUnary, windowUnary,
      thresholdUnary, routeUnary, routeReadUnary, martingaleWindowProof,
      provenancePkg, routeReadPkg⟩

end BEDC.Derived.UpcrossingUp
