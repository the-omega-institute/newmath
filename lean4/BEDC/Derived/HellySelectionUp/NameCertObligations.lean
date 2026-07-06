import BEDC.Derived.HellySelectionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HellySelectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HellySelectionCarrier [AskSetup] [PackageSetup]
    (B A W S R E T C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory T ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle N pkg

theorem HellySelection_namecert_obligations [AskSetup] [PackageSetup]
    {B A W S R E T C P N auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HellySelectionCarrier B A W S R E T C P N bundle pkg ->
      Cont E T auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row S ∨
                  hsame row R ∨ hsame row E ∨ hsame row auditRead)
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
              hsame ∧
            UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧
              UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier auditRoute auditPkg
  obtain ⟨bUnary, aUnary, wUnary, sUnary, rUnary, eUnary, tUnary, _cUnary, _pUnary,
    _nUnary, _namePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed eUnary tUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row auditRead)
          (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, auditPkg⟩
  }
  exact ⟨cert, bUnary, aUnary, wUnary, sUnary, rUnary, eUnary, auditUnary⟩

theorem HellySelection_public_export_namecert_consumer [AskSetup] [PackageSetup]
    {B A W S R E T C P N auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HellySelectionCarrier B A W S R E T C P N bundle pkg ->
      Cont E T auditRead ->
        PkgSig bundle auditRead pkg ->
          Cont auditRead C publicRead ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row S ∨
                    hsame row R ∨ hsame row E ∨ hsame row auditRead ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧
                    (PkgSig bundle auditRead pkg ∧ Cont auditRead C publicRead))
                hsame ∧
              UnaryHistory auditRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier auditRoute auditPkg publicRoute
  obtain ⟨auditCert, _bUnary, _aUnary, _wUnary, _sUnary, _rUnary, _eUnary,
    auditUnary⟩ :=
    HellySelection_namecert_obligations
      (B := B) (A := A) (W := W) (S := S) (R := R) (E := E) (T := T)
      (C := C) (P := P) (N := N) (auditRead := auditRead)
      (bundle := bundle) (pkg := pkg) carrier auditRoute auditPkg
  have ledgerWitness :
      Exists
        (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg) :=
    semanticNameCert_ledger_policy_witness auditCert
  obtain ⟨_bUnary, _aUnary, _wUnary, _sUnary, _rUnary, _eUnary, _tUnary, cUnary,
    _pUnary, _nUnary, _namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed auditUnary cUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row auditRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ (PkgSig bundle auditRead pkg ∧ Cont auditRead C publicRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditPkg, publicRoute⟩
  }
  cases ledgerWitness with
  | intro _auditLedger _auditLedgerPolicy =>
      exact ⟨cert, auditUnary, publicUnary⟩

theorem HellySelection_bounded_variation_window [AskSetup] [PackageSetup]
    {B A W S R E T C P N variationRead boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HellySelectionCarrier B A W S R E T C P N bundle pkg ->
      Cont B A variationRead ->
        Cont variationRead W boundedRead ->
          PkgSig bundle boundedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row boundedRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle boundedRead pkg)
                hsame ∧
              UnaryHistory variationRead ∧ UnaryHistory boundedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier variationRoute boundedRoute boundedPkg
  obtain ⟨bUnary, aUnary, wUnary, _sUnary, _rUnary, _eUnary, _tUnary, _cUnary,
    _pUnary, _nUnary, _namePkg⟩ := carrier
  have variationUnary : UnaryHistory variationRead :=
    unary_cont_closed bUnary aUnary variationRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed variationUnary wUnary boundedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row boundedRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle boundedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundedRead ⟨hsame_refl boundedRead, boundedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundedPkg⟩
  }
  exact ⟨cert, variationUnary, boundedUnary⟩

theorem HellySelection_finite_variation_window_handoff [AskSetup] [PackageSetup]
    {B A W S R E T C P N variationRead boundedRead selectedRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HellySelectionCarrier B A W S R E T C P N bundle pkg ->
      Cont B A variationRead ->
        Cont variationRead W boundedRead ->
          Cont S R selectedRead ->
            Cont selectedRead E sealedRead ->
              PkgSig bundle sealedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row S ∨
                        hsame row R ∨ hsame row E ∨ hsame row sealedRead)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealedRead pkg)
                    hsame ∧
                  UnaryHistory boundedRead ∧ UnaryHistory selectedRead ∧
                    UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier variationRoute boundedRoute selectedRoute sealedRoute sealedPkg
  obtain ⟨bUnary, aUnary, wUnary, sUnary, rUnary, eUnary, _tUnary, _cUnary,
    _pUnary, _nUnary, _namePkg⟩ := carrier
  have variationUnary : UnaryHistory variationRead :=
    unary_cont_closed bUnary aUnary variationRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed variationUnary wUnary boundedRoute
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed sUnary rUnary selectedRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed selectedUnary eUnary sealedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row sealedRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealedPkg⟩
  }
  exact ⟨cert, boundedUnary, selectedUnary, sealedUnary⟩

theorem HellySelection_subsequence_handoff [AskSetup] [PackageSetup]
    {B A W S R E T C P N selectedRead sealedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HellySelectionCarrier B A W S R E T C P N bundle pkg ->
      Cont S R selectedRead ->
        Cont selectedRead E sealedRead ->
          Cont sealedRead T replayRead ->
            PkgSig bundle replayRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                      hsame row replayRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle replayRead pkg)
                  hsame ∧
                UnaryHistory selectedRead ∧ UnaryHistory sealedRead ∧
                  UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier selectedRoute sealedRoute replayRoute replayPkg
  obtain ⟨_bUnary, _aUnary, _wUnary, sUnary, rUnary, eUnary, tUnary, _cUnary,
    _pUnary, _nUnary, _namePkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed sUnary rUnary selectedRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed selectedUnary eUnary sealedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealedUnary tUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
              hsame row replayRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayPkg⟩
  }
  exact ⟨cert, selectedUnary, sealedUnary, replayUnary⟩

end BEDC.Derived.HellySelectionUp
