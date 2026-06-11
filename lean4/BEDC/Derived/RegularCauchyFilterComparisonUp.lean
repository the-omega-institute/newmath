import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyFilterComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyFilterComparisonCarrier [AskSetup] [PackageSetup]
    (F B T S D R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory F ∧ UnaryHistory B ∧ UnaryHistory T ∧ UnaryHistory S ∧
    UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont B T S ∧ Cont D R C ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RegularCauchyFilterComparisonSequentialHandoff [AskSetup] [PackageSetup]
    {F B T S D R H C P N tailRead obsRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyFilterComparisonCarrier F B T S D R H C P N bundle pkg →
      Cont B T tailRead →
        Cont tailRead S obsRead →
          Cont D R sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row F ∨ hsame row B ∨ hsame row T ∨ hsame row S ∨
                      hsame row D ∨ hsame row R ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B T tailRead ∧ Cont tailRead S obsRead ∧
                      Cont D R sealRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory tailRead ∧ UnaryHistory obsRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier tailRoute obsRoute sealRoute sealPkg
  obtain ⟨fUnary, bUnary, tUnary, sUnary, dUnary, rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _baseTailRoute, _sealReplayRoute, provenancePkg, _localPkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed bUnary tUnary tailRoute
  have obsUnary : UnaryHistory obsRead :=
    unary_cont_closed tailUnary sUnary obsRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dUnary rUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row B ∨ hsame row T ∨ hsame row S ∨ hsame row D ∨
              hsame row R ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B T tailRead ∧ Cont tailRead S obsRead ∧
              Cont D R sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, tailRoute, obsRoute, sealRoute, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, tailUnary, obsUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyFilterComparisonUp
