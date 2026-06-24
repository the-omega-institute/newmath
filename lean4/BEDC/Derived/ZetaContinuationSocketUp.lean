import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZetaContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZetaContinuationSocketCarrier [AskSetup] [PackageSetup]
    (basic eta analytic pole functional trivial gamma transport route name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory basic ∧ UnaryHistory eta ∧ UnaryHistory analytic ∧ UnaryHistory pole ∧
    UnaryHistory functional ∧ UnaryHistory trivial ∧ UnaryHistory gamma ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory name ∧
        Cont basic eta analytic ∧ Cont pole functional trivial ∧
          Cont gamma transport route ∧ PkgSig bundle route pkg ∧ PkgSig bundle name pkg

theorem ZetaContinuationSocketNameCertObligations [AskSetup] [PackageSetup]
    {basic eta analytic pole functional trivial gamma transport route name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationSocketCarrier basic eta analytic pole functional trivial gamma transport
      route name bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                hsame row transport ∨ hsame row route ∨ hsame row name)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont basic eta analytic ∧
              Cont pole functional trivial ∧ Cont gamma transport route ∧
                PkgSig bundle route pkg ∧ PkgSig bundle name pkg)
          hsame ∧ UnaryHistory analytic ∧ UnaryHistory functional ∧ UnaryHistory route := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨_basicUnary, _etaUnary, analyticUnary, _poleUnary, functionalUnary,
    _trivialUnary, _gammaUnary, _transportUnary, routeUnary, nameUnary, analyticRoute,
    trivialRoute, routeRoute, routePkg, namePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                hsame row transport ∨ hsame row route ∨ hsame row name)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont basic eta analytic ∧
              Cont pole functional trivial ∧ Cont gamma transport route ∧
                PkgSig bundle route pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name ⟨hsame_refl name, nameUnary⟩
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
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, analyticRoute, trivialRoute, routeRoute, routePkg, namePkg⟩
  }
  exact ⟨cert, analyticUnary, functionalUnary, routeUnary⟩

end BEDC.Derived.ZetaContinuationSocketUp
