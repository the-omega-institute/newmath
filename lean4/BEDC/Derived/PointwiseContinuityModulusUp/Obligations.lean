import BEDC.Derived.PointwiseContinuityModulusUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PointwiseContinuityModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PointwiseContinuityModulusCarrier [AskSetup] [PackageSetup]
    (X Y F x eps delta R U K H C Q N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory F ∧ UnaryHistory x ∧
    UnaryHistory eps ∧ UnaryHistory delta ∧ UnaryHistory R ∧
      UnaryHistory U ∧ UnaryHistory K ∧ UnaryHistory H ∧ UnaryHistory C ∧
        UnaryHistory Q ∧ UnaryHistory N ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg

theorem PointwiseContinuityModulusCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X Y F x eps delta R U K H C Q N radiusRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PointwiseContinuityModulusCarrier X Y F x eps delta R U K H C Q N bundle pkg ->
      Cont eps delta radiusRead ->
        Cont radiusRead K compactRead ->
          PkgSig bundle compactRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row x ∨
                    hsame row eps ∨ hsame row delta ∨ hsame row R ∨ hsame row U ∨
                      hsame row K ∨ hsame row H ∨ hsame row C ∨ hsame row Q ∨
                        hsame row N ∨ hsame row compactRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
                    PkgSig bundle compactRead pkg)
                hsame ∧
              UnaryHistory radiusRead ∧ UnaryHistory compactRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier radiusRoute compactRoute compactPkg
  obtain ⟨_xUnary, _yUnary, _fUnary, _pointUnary, epsUnary, deltaUnary, _rUnary,
    _uUnary, kUnary, _hUnary, _cUnary, qUnary, nUnary, provenancePkg,
    localNamePkg⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed epsUnary deltaUnary radiusRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary kUnary compactRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row x ∨
              hsame row eps ∨ hsame row delta ∨ hsame row R ∨ hsame row U ∨
                hsame row K ∨ hsame row H ∨ hsame row C ∨ hsame row Q ∨
                  hsame row N ∨ hsame row compactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
              PkgSig bundle compactRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨compactRead, hsame_refl compactRead, compactUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other last sameRO sameOL
        exact hsame_trans sameRO sameOL
      carrier_respects_equiv := by
        intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left,
          unary_transport source.right same⟩
    }
    pattern_sound := by
      intro row source
      repeat apply Or.inr
      exact source.left
    ledger_sound := by
      intro row source
      exact ⟨source.right, provenancePkg, localNamePkg, compactPkg⟩
  }
  exact ⟨cert, radiusUnary, compactUnary⟩

end BEDC.Derived.PointwiseContinuityModulusUp
