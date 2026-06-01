import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_adjacency_density [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N gapRead mediantRead densityRead
      approximationRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A gapRead ->
        Cont gapRead M mediantRead ->
          Cont mediantRead S densityRead ->
            Cont densityRead D approximationRead ->
              Cont approximationRead G sealedRead ->
                PkgSig bundle sealedRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row densityRead ∨ hsame row sealedRead)
                      (fun row : BHist =>
                        hsame row gapRead ∨ hsame row mediantRead ∨
                          hsame row densityRead ∨ hsame row sealedRead)
                      (fun row : BHist =>
                        PkgSig bundle P pkg ∧
                          (hsame row densityRead ∨ hsame row sealedRead))
                      hsame ∧
                    UnaryHistory gapRead ∧
                      UnaryHistory mediantRead ∧
                        UnaryHistory densityRead ∧ UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier gapRoute mediantRoute densityRoute approximationRoute sealRoute sealedPkg
  obtain ⟨bUnary, aUnary, mUnary, _lUnary, _tUnary, sUnary, dUnary, _qUnary, _wUnary,
    _rUnary, gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary, _aEmpty, _sEmpty,
    _mEmpty, _gEmpty, _eEmpty, provenancePkg⟩ := carrier
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed bUnary aUnary gapRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed gapUnary mUnary mediantRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed mediantUnary sUnary densityRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed densityUnary dUnary approximationRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed approximationUnary gUnary sealRoute
  have _sealedPackage : PkgSig bundle sealedRead pkg := sealedPkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∨ hsame row sealedRead)
          (fun row : BHist =>
            hsame row gapRead ∨ hsame row mediantRead ∨ hsame row densityRead ∨
              hsame row sealedRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ (hsame row densityRead ∨ hsame row sealedRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead (Or.inr (hsame_refl sealedRead))
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameDensity =>
          exact Or.inr (Or.inr (Or.inl sameDensity))
      | inr sameSeal =>
          exact Or.inr (Or.inr (Or.inr sameSeal))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source⟩
  }
  exact ⟨cert, gapUnary, mediantUnary, densityUnary, sealedUnary⟩

end BEDC.Derived.FareySequenceUp
