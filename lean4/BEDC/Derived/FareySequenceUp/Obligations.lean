import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Package.Core
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_adjacency_obligation [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacencyRead sternRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A adjacencyRead ->
        Cont A S sternRead ->
          PkgSig bundle P pkg ->
            UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory S ∧
              UnaryHistory adjacencyRead ∧ UnaryHistory sternRead ∧
                Cont B A adjacencyRead ∧ Cont A S sternRead ∧
                  hsame adjacencyRead (append B A) ∧ hsame sternRead (append A S) ∧
                    PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier adjacencyRoute sternRoute pkgSig
  obtain ⟨bUnary, aUnary, _mUnary, _lUnary, _tUnary, sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _storedPkgSig⟩ := carrier
  have adjacencyUnary : UnaryHistory adjacencyRead :=
    unary_cont_closed bUnary aUnary adjacencyRoute
  have sternUnary : UnaryHistory sternRead :=
    unary_cont_closed aUnary sUnary sternRoute
  have adjacencyExact : hsame adjacencyRead (append B A) := by
    cases adjacencyRoute
    exact hsame_refl _
  have sternExact : hsame sternRead (append A S) := by
    cases sternRoute
    exact hsame_refl _
  exact
    ⟨bUnary, aUnary, sUnary, adjacencyUnary, sternUnary, adjacencyRoute, sternRoute,
      adjacencyExact, sternExact, pkgSig⟩

theorem FareySequenceCarrier_refinement_obligation [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N mediantRead toleranceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont M L mediantRead ->
        Cont mediantRead T toleranceRead ->
          PkgSig bundle P pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row mediantRead ∨ hsame row toleranceRead)
                (fun row : BHist =>
                  hsame row M ∨ hsame row L ∨ hsame row T ∨ hsame row S ∨
                    hsame row mediantRead ∨ hsame row toleranceRead)
                (fun row : BHist =>
                  PkgSig bundle P pkg ∧
                    (hsame row mediantRead ∨ hsame row toleranceRead))
                hsame ∧
              UnaryHistory mediantRead ∧ UnaryHistory toleranceRead ∧
                PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier mediantRoute toleranceRoute pkgSig
  obtain ⟨_bUnary, _aUnary, mUnary, lUnary, tUnary, _sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _storedPkgSig⟩ := carrier
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed mUnary lUnary mediantRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed mediantUnary tUnary toleranceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row mediantRead ∨ hsame row toleranceRead)
          (fun row : BHist =>
            hsame row M ∨ hsame row L ∨ hsame row T ∨ hsame row S ∨
              hsame row mediantRead ∨ hsame row toleranceRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ (hsame row mediantRead ∨ hsame row toleranceRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro mediantRead (Or.inl (hsame_refl mediantRead))
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
        intro _row other sameRows source
        cases source with
        | inl sameMediant =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameMediant)
        | inr sameTolerance =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameTolerance)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameMediant =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameMediant))))
      | inr sameTolerance =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameTolerance))))
    ledger_sound := by
      intro _row source
      exact ⟨pkgSig, source⟩
  }
  exact ⟨cert, mediantUnary, toleranceUnary, pkgSig⟩

end BEDC.Derived.FareySequenceUp
