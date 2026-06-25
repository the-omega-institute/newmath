import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationSourceCoverLocality [AskSetup] [PackageSetup] :
    forall {C T J P L G S H R Q N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg},
      SheafificationCarrier C T J P L G S H R Q N bundle pkg ->
        PkgSig bundle N pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P)
            (fun row : BHist =>
              hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨ hsame row L)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro C T J P L G S H R Q N bundle pkg carrier namePkg
  obtain ⟨cUnary, tUnary, jUnary, pUnary, _lUnary, _gUnary, _sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  constructor
  · constructor
    · exact ⟨C, Or.inl (hsame_refl C)⟩
    · intro row _source
      exact hsame_refl row
    · intro row other same
      exact hsame_symm same
    · intro row middle other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro row other same source
      cases source with
      | inl rowC =>
          exact Or.inl (hsame_trans (hsame_symm same) rowC)
      | inr rest =>
          cases rest with
          | inl rowT =>
              exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowT))
          | inr rest =>
              cases rest with
              | inl rowJ =>
                  exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowJ)))
              | inr rowP =>
                  exact Or.inr (Or.inr (Or.inr (hsame_trans (hsame_symm same) rowP)))
  · intro row source
    cases source with
    | inl rowC =>
        exact Or.inl rowC
    | inr rest =>
        cases rest with
        | inl rowT =>
            exact Or.inr (Or.inl rowT)
        | inr rest =>
            cases rest with
            | inl rowJ =>
                exact Or.inr (Or.inr (Or.inl rowJ))
            | inr rowP =>
                exact Or.inr (Or.inr (Or.inr (Or.inl rowP)))
  · intro row source
    cases source with
    | inl rowC =>
        cases rowC
        exact ⟨cUnary, namePkg⟩
    | inr rest =>
        cases rest with
        | inl rowT =>
            cases rowT
            exact ⟨tUnary, namePkg⟩
        | inr rest =>
            cases rest with
            | inl rowJ =>
                cases rowJ
                exact ⟨jUnary, namePkg⟩
            | inr rowP =>
                cases rowP
                exact ⟨pUnary, namePkg⟩

end BEDC.Derived.SheafificationUp
