import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MazurUlamIsometryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MazurUlamIsometryCarrier [AskSetup] [PackageSetup]
    (E F G M A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory E ∧ UnaryHistory F ∧ UnaryHistory G ∧ UnaryHistory M ∧
    UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg

theorem MazurUlamIsometryCarrier_midpoint_preservation [AskSetup] [PackageSetup]
    {E F G M A H C P N midpointRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MazurUlamIsometryCarrier E F G M A H C P N bundle pkg ->
      Cont G M midpointRead ->
        Cont midpointRead H targetRead ->
          PkgSig bundle P pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row G ∨ hsame row M ∨ hsame row midpointRead ∨
                    hsame row targetRead) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row E ∨ hsame row F ∨ hsame row G ∨ hsame row M ∨
                    hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row midpointRead ∨ hsame row targetRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont G M midpointRead ∧
                    Cont midpointRead H targetRead ∧ PkgSig bundle P pkg)
                hsame ∧
              UnaryHistory midpointRead ∧ UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: MazurUlamIsometryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier midpointRoute targetRoute provenancePkg
  obtain ⟨_eUnary, _fUnary, gUnary, mUnary, _aUnary, hUnary, _cUnary, _pUnary,
    _nUnary, _carrierPkg⟩ := carrier
  have midpointUnary : UnaryHistory midpointRead :=
    unary_cont_closed gUnary mUnary midpointRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed midpointUnary hUnary targetRoute
  have source :
      (fun row : BHist =>
        (hsame row G ∨ hsame row M ∨ hsame row midpointRead ∨ hsame row targetRead) ∧
          UnaryHistory row) midpointRead := by
    exact ⟨Or.inr (Or.inr (Or.inl (hsame_refl midpointRead))), midpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row G ∨ hsame row M ∨ hsame row midpointRead ∨ hsame row targetRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row F ∨ hsame row G ∨ hsame row M ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row midpointRead ∨ hsame row targetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont G M midpointRead ∧ Cont midpointRead H targetRead ∧
              PkgSig bundle P pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro midpointRead source
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
          intro _row _other sameRows sourceRows
          constructor
          · cases sourceRows.left with
            | inl sameG =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameG)
            | inr rest =>
                cases rest with
                | inl sameM =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameM))
                | inr rest =>
                    cases rest with
                    | inl sameMidpoint =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameMidpoint)))
                    | inr sameTarget =>
                        exact
                          Or.inr
                            (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameTarget)))
          · exact unary_transport sourceRows.right sameRows
      }
      pattern_sound := by
        intro _row sourceRows
        cases sourceRows.left with
        | inl sameG =>
            exact Or.inr (Or.inr (Or.inl sameG))
        | inr rest =>
            cases rest with
            | inl sameM =>
                exact Or.inr (Or.inr (Or.inr (Or.inl sameM)))
            | inr rest =>
                cases rest with
                | inl sameMidpoint =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inl sameMidpoint)))))))))
                | inr sameTarget =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inr sameTarget)))))))))
      ledger_sound := by
        intro _row sourceRows
        exact ⟨sourceRows.right, midpointRoute, targetRoute, provenancePkg⟩
    }
  exact ⟨cert, midpointUnary, targetUnary⟩

end BEDC.Derived.MazurUlamIsometryUp
