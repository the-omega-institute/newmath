import BEDC.Derived.CauchyFilterClusterUp.NameCertObligations

namespace BEDC.Derived.CauchyFilterClusterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterClusterClusterRoute [AskSetup] [PackageSetup]
    {F M U W Q S D E H C P N retainedWindow clusterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterClusterCarrier F M U W Q S D E H C P N bundle pkg →
      Cont M U retainedWindow →
        Cont retainedWindow W clusterRead →
          PkgSig bundle clusterRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row clusterRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row F ∨ hsame row M ∨ hsame row U ∨ hsame row W ∨
                    hsame row Q ∨ hsame row S ∨ hsame row D ∨ hsame row clusterRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont M U retainedWindow ∧
                    Cont retainedWindow W clusterRead ∧ PkgSig bundle clusterRead pkg)
                hsame ∧ UnaryHistory retainedWindow ∧ UnaryHistory clusterRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier retainedRoute clusterRoute clusterPkg
  obtain ⟨_fUnary, mUnary, uUnary, wUnary, _qUnary, _sUnary, _dUnary, _eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _namePkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed mUnary uUnary retainedRoute
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed retainedUnary wUnary clusterRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row clusterRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row M ∨ hsame row U ∨ hsame row W ∨ hsame row Q ∨
              hsame row S ∨ hsame row D ∨ hsame row clusterRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M U retainedWindow ∧
              Cont retainedWindow W clusterRead ∧ PkgSig bundle clusterRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro clusterRead ⟨hsame_refl clusterRead, clusterUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, retainedRoute, clusterRoute, clusterPkg⟩
  }
  exact ⟨cert, retainedUnary, clusterUnary⟩

end BEDC.Derived.CauchyFilterClusterUp
