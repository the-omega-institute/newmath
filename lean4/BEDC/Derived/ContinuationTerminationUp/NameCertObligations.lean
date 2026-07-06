import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuationTerminationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContinuationTerminationObligationRowSpec
    (s t tau u b h p n row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame
  hsame row s ∨ hsame row t ∨ hsame row tau ∨ hsame row u ∨
    hsame row b ∨ hsame row h ∨ hsame row p ∨ hsame row n

theorem ContinuationTerminationCarrier_namecert_obligations
    (s t tau u b h p n : BHist) :
    SemanticNameCert
      (ContinuationTerminationObligationRowSpec s t tau u b h p n)
      (ContinuationTerminationObligationRowSpec s t tau u b h p n)
      (ContinuationTerminationObligationRowSpec s t tau u b h p n)
      hsame ∧
      ContinuationTerminationObligationRowSpec s t tau u b h p n s ∧
        ContinuationTerminationObligationRowSpec s t tau u b h p n t ∧
          ContinuationTerminationObligationRowSpec s t tau u b h p n tau := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  constructor
  · exact
      {
        core := {
          carrier_inhabited := Exists.intro s (Or.inl (hsame_refl s))
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro row col same
            exact hsame_symm same
          equiv_trans := by
            intro row col target sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row col same source
            cases source with
            | inl sourceS =>
                exact Or.inl (hsame_trans (hsame_symm same) sourceS)
            | inr rest =>
                cases rest with
                | inl sourceT =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sourceT))
                | inr rest =>
                    cases rest with
                    | inl sourceTau =>
                        exact Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm same) sourceTau)))
                    | inr rest =>
                        cases rest with
                        | inl sourceU =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm same) sourceU))))
                        | inr rest =>
                            cases rest with
                            | inl sourceB =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl (hsame_trans (hsame_symm same) sourceB)))))
                            | inr rest =>
                                cases rest with
                                | inl sourceH =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans (hsame_symm same) sourceH))))))
                                | inr rest =>
                                    cases rest with
                                    | inl sourceP =>
                                        exact Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inl
                                                      (hsame_trans (hsame_symm same)
                                                        sourceP)))))))
                                    | inr sourceN =>
                                        exact Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (hsame_trans (hsame_symm same)
                                                        sourceN)))))))
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }
  · constructor
    · exact Or.inl (hsame_refl s)
    · constructor
      · exact Or.inr (Or.inl (hsame_refl t))
      · exact Or.inr (Or.inr (Or.inl (hsame_refl tau)))

def ContinuationTerminationCarrier [AskSetup] [PackageSetup]
    (s t tau u b h p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  UnaryHistory s ∧ UnaryHistory t ∧ Cont s t tau ∧
    hsame u u ∧ hsame b b ∧ hsame h h ∧
      PkgSig bundle p pkg ∧ PkgSig bundle n pkg

def ContinuationTerminationClassifier
    (s t tau u b h p n s' t' tau' u' b' h' p' n' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame
  hsame s s' ∧ hsame t t' ∧ hsame tau tau' ∧ Cont s' t' tau' ∧
    hsame u u' ∧ hsame b b' ∧ hsame h h' ∧ hsame p p' ∧ hsame n n'

theorem ContinuationTerminationCarrier_classifier_stability [AskSetup] [PackageSetup]
    {s t tau u b h p n s' t' tau' u' b' h' p' n' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationTerminationCarrier s t tau u b h p n bundle pkg →
      ContinuationTerminationClassifier s t tau u b h p n s' t' tau' u' b' h' p' n' →
        UnaryHistory s' ∧ UnaryHistory t' ∧ Cont s' t' tau' ∧ hsame u u' ∧
          hsame b b' ∧ hsame h h' ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro carrier classifier
  obtain ⟨sUnary, tUnary, route, _sameU, _sameB, _sameH, pPkg, nPkg⟩ := carrier
  obtain ⟨sameS, sameT, sameTrace, route', sameU', sameB', sameH', _sameP',
    _sameN'⟩ := classifier
  have sUnary' : UnaryHistory s' := unary_transport sUnary sameS
  have tUnary' : UnaryHistory t' := unary_transport tUnary sameT
  have _sameTraceFromRoutes : hsame tau tau' := cont_respects_hsame sameS sameT route route'
  have _traceComponent : hsame tau tau' := sameTrace
  exact ⟨sUnary', tUnary', route', sameU', sameB', sameH', pPkg, nPkg⟩

theorem ContinuationTerminationClassifier_route_exactness [AskSetup] [PackageSetup]
    {s t tau u b h p n s' t' tau' u' b' h' p' n' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationTerminationCarrier s t tau u b h p n bundle pkg →
      ContinuationTerminationClassifier s t tau u b h p n s' t' tau' u' b' h' p' n' →
        UnaryHistory s' ∧ UnaryHistory t' ∧ hsame tau tau' ∧ Cont s' t' tau' ∧
          hsame u u' ∧ hsame b b' ∧ hsame h h' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier classifier
  obtain ⟨sUnary, tUnary, _route, _sameU, _sameB, _sameH, _pPkg, _nPkg⟩ := carrier
  obtain ⟨sameS, sameT, sameTau, route', sameU', sameB', sameH', _sameP',
    _sameN'⟩ := classifier
  have sUnary' : UnaryHistory s' := unary_transport sUnary sameS
  have tUnary' : UnaryHistory t' := unary_transport tUnary sameT
  exact ⟨sUnary', tUnary', sameTau, route', sameU', sameB', sameH'⟩

end BEDC.Derived.ContinuationTerminationUp
