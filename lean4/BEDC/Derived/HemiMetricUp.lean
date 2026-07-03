import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HemiMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HemiMetricCarrier [AskSetup] [PackageSetup]
    (S X D Z T B Q L M U R K C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory S ∧ UnaryHistory X ∧ UnaryHistory D ∧ UnaryHistory Z ∧
    UnaryHistory T ∧ UnaryHistory B ∧ UnaryHistory Q ∧ UnaryHistory L ∧
      UnaryHistory M ∧ UnaryHistory U ∧ UnaryHistory R ∧ UnaryHistory K ∧
        UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg

theorem HemiMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S X D Z T B Q L M U R K C P N nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HemiMetricCarrier S X D Z T B Q L M U R K C P N bundle pkg ->
      PkgSig bundle N pkg ->
        Cont R K nameRead ->
          SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row X ∨ hsame row D ∨ hsame row Z ∨
                  hsame row T ∨ hsame row B ∨ hsame row Q ∨ hsame row L ∨
                    hsame row M ∨ hsame row U ∨ hsame row R ∨ hsame row K ∨
                      hsame row C ∨ hsame row P ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont R K nameRead ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: HemiMetricCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier namePkg nameRoute
  obtain ⟨_sUnary, _xUnary, _dUnary, _zUnary, _tUnary, _bUnary, _qUnary, _lUnary,
    _mUnary, _uUnary, rUnary, kUnary, _cUnary, _pUnary, nUnary, _pPkg,
    _storedNamePkg⟩ := carrier
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed rUnary kUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row X ∨ hsame row D ∨ hsame row Z ∨
              hsame row T ∨ hsame row B ∨ hsame row Q ∨ hsame row L ∨
                hsame row M ∨ hsame row U ∨ hsame row R ∨ hsame row K ∨
                  hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R K nameRead ∧ PkgSig bundle N pkg)
          hsame := {
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
      exact ⟨source.right, nameRoute, namePkg⟩
  }
  exact ⟨cert, nameReadUnary⟩

theorem HemiMetricCarrier_directed_ball_handoff [AskSetup] [PackageSetup]
    {S X D Z T B Q L M U R K C P N ballRead handoffRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HemiMetricCarrier S X D Z T B Q L M U R K C P N bundle pkg ->
      Cont T B ballRead ->
        Cont ballRead U handoffRead ->
          Cont R K nameRead ->
            PkgSig bundle N pkg ->
              UnaryHistory ballRead ∧ UnaryHistory handoffRead ∧
                UnaryHistory nameRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: HemiMetricCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier ballRoute handoffRoute nameRoute namePkg
  obtain ⟨_sUnary, _xUnary, _dUnary, _zUnary, tUnary, bUnary, _qUnary, _lUnary,
    _mUnary, uUnary, rUnary, kUnary, _cUnary, _pUnary, _nUnary, pPkg,
    _storedNamePkg⟩ := carrier
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed tUnary bUnary ballRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed ballReadUnary uUnary handoffRoute
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed rUnary kUnary nameRoute
  exact ⟨ballReadUnary, handoffReadUnary, nameReadUnary, pPkg, namePkg⟩

end BEDC.Derived.HemiMetricUp
