import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceAdjacencyObligation [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacencyRead mediantRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont A S adjacencyRead ->
        Cont adjacencyRead M mediantRead ->
          PkgSig bundle P pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row adjacencyRead ∨ hsame row mediantRead)
                (fun row : BHist =>
                  hsame row A ∨ hsame row S ∨ hsame row M ∨ hsame row adjacencyRead ∨
                    hsame row mediantRead)
                (fun row : BHist =>
                  PkgSig bundle P pkg ∧ (hsame row adjacencyRead ∨ hsame row mediantRead))
                hsame ∧
              UnaryHistory adjacencyRead ∧ UnaryHistory mediantRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier adjacencyRoute mediantRoute provenancePkg
  obtain ⟨_bUnary, aUnary, mUnary, _lUnary, _tUnary, sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have adjacencyUnary : UnaryHistory adjacencyRead :=
    unary_cont_closed aUnary sUnary adjacencyRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed adjacencyUnary mUnary mediantRoute
  have sourceAdjacency :
      (fun row : BHist => hsame row adjacencyRead ∨ hsame row mediantRead)
        adjacencyRead := by
    exact Or.inl (hsame_refl adjacencyRead)
  have sourcePattern :
      ∀ {row : BHist},
        (hsame row adjacencyRead ∨ hsame row mediantRead) →
          hsame row A ∨ hsame row S ∨ hsame row M ∨ hsame row adjacencyRead ∨
            hsame row mediantRead := by
    intro _row source
    cases source with
    | inl sameAdjacency =>
        exact Or.inr (Or.inr (Or.inr (Or.inl sameAdjacency)))
    | inr sameMediant =>
        exact Or.inr (Or.inr (Or.inr (Or.inr sameMediant)))
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row adjacencyRead ∨ hsame row mediantRead)
          (fun row : BHist =>
            hsame row A ∨ hsame row S ∨ hsame row M ∨ hsame row adjacencyRead ∨
              hsame row mediantRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ (hsame row adjacencyRead ∨ hsame row mediantRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro adjacencyRead sourceAdjacency
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
        | inl sameAdjacency =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameAdjacency)
        | inr sameMediant =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameMediant)
    }
    pattern_sound := by
      intro _row source
      exact sourcePattern source
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source⟩
  }
  exact ⟨cert, adjacencyUnary, mediantUnary⟩

end BEDC.Derived.FareySequenceUp
