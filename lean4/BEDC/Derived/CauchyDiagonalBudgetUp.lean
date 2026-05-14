import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyDiagonalBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyDiagonalBudgetCarrier [AskSetup] [PackageSetup]
    (epsilon m w d k s h c p name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory epsilon ∧ UnaryHistory m ∧ UnaryHistory w ∧ UnaryHistory d ∧
    UnaryHistory k ∧ UnaryHistory s ∧ UnaryHistory h ∧ UnaryHistory c ∧
      UnaryHistory p ∧ UnaryHistory name ∧ Cont epsilon m w ∧ Cont w d k ∧
        Cont k s h ∧ Cont h c p ∧ Cont c p name ∧ PkgSig bundle p pkg

theorem CauchyDiagonalBudgetCarrier_selection_determinacy [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name route sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg →
      Cont epsilon m route →
        Cont k s sealRow →
          PkgSig bundle sealRow pkg →
            UnaryHistory epsilon ∧ UnaryHistory m ∧ UnaryHistory w ∧ UnaryHistory d ∧
              UnaryHistory k ∧ UnaryHistory s ∧ UnaryHistory route ∧ UnaryHistory sealRow ∧
                Cont epsilon m route ∧ Cont k s sealRow ∧ PkgSig bundle sealRow pkg ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row p ∧ UnaryHistory row)
                    (fun row : BHist => hsame row p)
                    (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
                    hsame := by
  intro carrier routeRow sealRoute sealPkg
  have epsilonUnary : UnaryHistory epsilon := carrier.left
  have mUnary : UnaryHistory m := carrier.right.left
  have wUnary : UnaryHistory w := carrier.right.right.left
  have dUnary : UnaryHistory d := carrier.right.right.right.left
  have kUnary : UnaryHistory k := carrier.right.right.right.right.left
  have sUnary : UnaryHistory s := carrier.right.right.right.right.right.left
  have pUnary : UnaryHistory p :=
    carrier.right.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle p pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have routeUnary : UnaryHistory route :=
    unary_cont_closed epsilonUnary mUnary routeRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed kUnary sUnary sealRoute
  have sourceP :
      (fun row : BHist => hsame row p ∧ UnaryHistory row) p := by
    exact ⟨hsame_refl p, pUnary⟩
  have core :
      NameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro p sourceP
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' same source
        have sameRow' : hsame row' p :=
          hsame_trans (hsame_symm same) source.left
        exact ⟨sameRow', unary_transport source.right same⟩
    }
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        (fun row : BHist => hsame row p)
        (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact source.left
      ledger_sound := by
        intro row source
        exact ⟨source.left, pPkg⟩
    }
  exact
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, routeUnary, sealUnary,
      routeRow, sealRoute, sealPkg, cert⟩

theorem CauchyDiagonalBudget_route_factorization [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ->
      Cont h c endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ∧
                hsame row endpoint)
            (fun _row : BHist =>
              Cont epsilon m w ∧ Cont w d k ∧ Cont k s h ∧ Cont h c endpoint ∧
                PkgSig bundle endpoint pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier endpointRoute endpointPkg
  rcases carrier with
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
      nameUnary, epsilonMW, wDK, kSH, _hCP, cPName, pPkg⟩
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary endpointRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro
          ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
            nameUnary, epsilonMW, wDK, kSH, _hCP, cPName, pPkg⟩
          (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact ⟨epsilonMW, wDK, kSH, endpointRoute, endpointPkg⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport endpointUnary (hsame_symm source.right), endpointPkg⟩
  }

theorem CauchyDiagonalBudgetCarrier_real_completeness_handoff [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name sealEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg →
      Cont k s sealEndpoint →
        PkgSig bundle sealEndpoint pkg →
          SemanticNameCert
            (fun row : BHist =>
              CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ∧
                hsame row sealEndpoint)
            (fun _row : BHist => Cont epsilon m w ∧ Cont w d k ∧ Cont k s sealEndpoint)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealEndpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier sealRoute sealPkg
  rcases carrier with
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
      nameUnary, epsilonMW, wDK, kSH, hCP, cPName, pPkg⟩
  have sealUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed kUnary sUnary sealRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealEndpoint (And.intro
          ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
            nameUnary, epsilonMW, wDK, kSH, hCP, cPName, pPkg⟩
          (hsame_refl sealEndpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact ⟨epsilonMW, wDK, sealRoute⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport sealUnary (hsame_symm source.right), sealPkg⟩
  }

end BEDC.Derived.CauchyDiagonalBudgetUp
