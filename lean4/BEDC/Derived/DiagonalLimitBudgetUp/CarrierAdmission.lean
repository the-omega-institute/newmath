import BEDC.Derived.DiagonalLimitBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalLimitBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitBudgetCarrierAdmission [AskSetup] [PackageSetup]
    {x : DiagonalLimitBudgetUp}
    {D M W Q E H C P N requestBudget selectedWindow dyadicRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    x = DiagonalLimitBudgetUp.mk D M W Q E H C P N ->
      UnaryHistory D ->
        UnaryHistory M ->
          UnaryHistory W ->
            UnaryHistory Q ->
              UnaryHistory E ->
                Cont D M requestBudget ->
                  Cont requestBudget W selectedWindow ->
                    Cont selectedWindow Q dyadicRead ->
                      Cont dyadicRead E sealRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row D ∨ hsame row M ∨ hsame row W ∨
                                    hsame row Q ∨ hsame row E ∨ hsame row N ∨
                                      Cont dyadicRead E sealRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont D M requestBudget ∧
                                    Cont requestBudget W selectedWindow ∧
                                      Cont selectedWindow Q dyadicRead ∧
                                        Cont dyadicRead E sealRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory requestBudget ∧ UnaryHistory selectedWindow ∧
                                UnaryHistory dyadicRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier dUnary mUnary wUnary qUnary eUnary requestRoute windowRoute dyadicRoute
    sealRoute provenancePkg namePkg
  have _acceptedCarrier :
      x = DiagonalLimitBudgetUp.mk D M W Q E H C P N := carrier
  have requestUnary : UnaryHistory requestBudget :=
    unary_cont_closed dUnary mUnary requestRoute
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed requestUnary wUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed selectedUnary qUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row M ∨ hsame row W ∨ hsame row Q ∨ hsame row E ∨
              hsame row N ∨ Cont dyadicRead E sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D M requestBudget ∧
              Cont requestBudget W selectedWindow ∧ Cont selectedWindow Q dyadicRead ∧
                Cont dyadicRead E sealRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
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
      intro _row _source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sealRoute)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, requestRoute, windowRoute, dyadicRoute, sealRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, requestUnary, selectedUnary, dyadicUnary, sealUnary⟩

def DiagonalLimitBudgetCarrier [AskSetup] [PackageSetup]
    (D M W Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory W ∧ UnaryHistory Q ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont H C W ∧ Cont H C Q ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg

theorem DiagonalLimitBudgetSynchronizationStability [AskSetup] [PackageSetup]
    {D M W Q E H C P N Wread Qread Pread Nread : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitBudgetCarrier D M W Q E H C P N bundle pkg ->
      Cont H C Wread ->
        Cont H C Qread ->
          PkgSig bundle Pread pkg ->
            PkgSig bundle Nread pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row W ∨ hsame row Q ∨ hsame row P ∨ hsame row N) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row M ∨ hsame row W ∨ hsame row Q ∨
                      hsame row P ∨ hsame row N)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle Pread pkg ∧
                      PkgSig bundle Nread pkg)
                  hsame ∧
                UnaryHistory Wread ∧ UnaryHistory Qread := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier wreadRoute qreadRoute preadPkg nreadPkg
  obtain ⟨_dUnary, _mUnary, wUnary, qUnary, _eUnary, hUnary, cUnary, pUnary,
    nUnary, _windowRoute, _dyadicRoute, _provenancePkg, _namePkg⟩ := carrier
  have wreadUnary : UnaryHistory Wread :=
    unary_cont_closed hUnary cUnary wreadRoute
  have qreadUnary : UnaryHistory Qread :=
    unary_cont_closed hUnary cUnary qreadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row W ∨ hsame row Q ∨ hsame row P ∨ hsame row N) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row M ∨ hsame row W ∨ hsame row Q ∨
              hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle Pread pkg ∧
              PkgSig bundle Nread pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro W ⟨Or.inl (hsame_refl W), wUnary⟩
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
        constructor
        · cases source.left with
          | inl sameW =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameW)
          | inr tail =>
              cases tail with
              | inl sameQ =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameQ))
              | inr tail =>
                  cases tail with
                  | inl sameP =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameP)))
                  | inr sameN =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) sameN)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameW =>
          exact Or.inr (Or.inr (Or.inl sameW))
      | inr tail =>
          cases tail with
          | inl sameQ =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameQ)))
          | inr tail =>
              cases tail with
              | inl sameP =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameP))))
              | inr sameN =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameN))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, preadPkg, nreadPkg⟩
  }
  exact ⟨cert, wreadUnary, qreadUnary⟩

end BEDC.Derived.DiagonalLimitBudgetUp
