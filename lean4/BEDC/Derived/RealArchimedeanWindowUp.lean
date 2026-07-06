import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealArchimedeanWindowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealArchimedeanWindowCarrier [AskSetup] [PackageSetup]
    (R S Q D L U H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory D ∧
    UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont S Q D ∧ Cont H C P ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RealArchimedeanWindowNameCertObligations [AskSetup] [PackageSetup]
    {R S Q D L U H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealArchimedeanWindowCarrier R S Q D L U H C P N bundle pkg →
      PkgSig bundle P pkg →
        PkgSig bundle N pkg →
          SemanticNameCert
              (fun row : BHist =>
                RealArchimedeanWindowCarrier R S Q D L U H C P N bundle pkg ∧
                  hsame row N)
              (fun row : BHist =>
                hsame row R ∨ hsame row S ∨ hsame row Q ∨ hsame row D ∨
                  hsame row L ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧ UnaryHistory L ∧ UnaryHistory U ∧ Cont H C P := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier provenancePkg namePkg
  obtain ⟨rUnary, sUnary, qUnary, dUnary, lUnary, uUnary, hUnary, cUnary, pUnary,
    nUnary, readbackRoute, replay, _carrierPkg, _carrierName⟩ := carrier
  have carrierForSource :
      RealArchimedeanWindowCarrier R S Q D L U H C P N bundle pkg :=
    ⟨rUnary, sUnary, qUnary, dUnary, lUnary, uUnary, hUnary, cUnary, pUnary, nUnary,
      readbackRoute, replay, provenancePkg, namePkg⟩
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro N ⟨carrierForSource, hsame_refl N⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
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
        right
        right
        exact source.right
      ledger_sound := by
        intro _row source
        exact ⟨unary_transport nUnary (hsame_symm source.right), provenancePkg, namePkg⟩
    }
  · exact ⟨lUnary, uUnary, replay⟩

theorem RealArchimedeanWindowCarrier_bound_consumer_exactness [AskSetup] [PackageSetup]
    {R S Q D L U H C P N radiusRead boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealArchimedeanWindowCarrier R S Q D L U H C P N bundle pkg ->
      Cont D L radiusRead ->
        Cont radiusRead U boundRead ->
          PkgSig bundle boundRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row R ∨ hsame row S ∨ hsame row Q ∨ hsame row D ∨
                    hsame row L ∨ hsame row U ∨ hsame row radiusRead ∨ hsame row boundRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont S Q D ∧ Cont D L radiusRead ∧
                    Cont radiusRead U boundRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle boundRead pkg)
                hsame ∧ UnaryHistory boundRead := by
  -- BEDC touchpoint anchor: RealArchimedeanWindowCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier radiusRoute boundRoute boundPkg
  obtain ⟨_rUnary, _sUnary, _qUnary, dUnary, lUnary, uUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, readbackRoute, _replay, provenancePkg, _namePkg⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed dUnary lUnary radiusRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed radiusUnary uUnary boundRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row S ∨ hsame row Q ∨ hsame row D ∨ hsame row L ∨
              hsame row U ∨ hsame row radiusRead ∨ hsame row boundRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S Q D ∧ Cont D L radiusRead ∧
              Cont radiusRead U boundRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle boundRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundRead ⟨hsame_refl boundRead, boundUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, readbackRoute, radiusRoute, boundRoute, provenancePkg, boundPkg⟩
  }
  exact ⟨cert, boundUnary⟩

end BEDC.Derived.RealArchimedeanWindowUp
