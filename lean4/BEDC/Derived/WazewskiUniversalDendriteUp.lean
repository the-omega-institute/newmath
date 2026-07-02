import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WazewskiUniversalDendriteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WazewskiUniversalDendriteCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {D P L K T B E U H C Q N _branchRead subtreeRead universalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory P ->
        UnaryHistory L ->
          UnaryHistory K ->
            UnaryHistory T ->
              UnaryHistory B ->
                UnaryHistory E ->
                  UnaryHistory U ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        UnaryHistory Q ->
                          UnaryHistory N ->
                            Cont D P L ->
                              Cont K T B ->
                                Cont B E subtreeRead ->
                                  Cont subtreeRead U universalRead ->
                                    PkgSig bundle Q pkg ->
                                      PkgSig bundle N pkg ->
                                        PkgSig bundle universalRead pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row universalRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row D ∨ hsame row P ∨ hsame row L ∨
                                                  hsame row K ∨ hsame row T ∨ hsame row B ∨
                                                    hsame row E ∨ hsame row U ∨
                                                      hsame row universalRead ∨ hsame row N)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont D P L ∧
                                                  Cont K T B ∧ Cont B E subtreeRead ∧
                                                    Cont subtreeRead U universalRead ∧
                                                      PkgSig bundle Q pkg ∧
                                                        PkgSig bundle universalRead pkg)
                                              hsame ∧ UnaryHistory universalRead := by
  -- BEDC touchpoint anchor: WazewskiUniversalDendriteUp BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _dUnary _pUnary _lUnary _kUnary _tUnary bUnary eUnary uUnary _hUnary
    _cUnary _qUnary _nUnary continuumRoute branchRoute subtreeRoute universalRoute
    provenancePkg _namePkg universalPkg
  have subtreeUnary : UnaryHistory subtreeRead :=
    unary_cont_closed bUnary eUnary subtreeRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed subtreeUnary uUnary universalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row universalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row P ∨ hsame row L ∨ hsame row K ∨ hsame row T ∨
              hsame row B ∨ hsame row E ∨ hsame row U ∨ hsame row universalRead ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D P L ∧ Cont K T B ∧ Cont B E subtreeRead ∧
              Cont subtreeRead U universalRead ∧ PkgSig bundle Q pkg ∧
                PkgSig bundle universalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro universalRead ⟨hsame_refl universalRead, universalUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, continuumRoute, branchRoute, subtreeRoute, universalRoute,
          provenancePkg, universalPkg⟩
  }
  exact ⟨cert, universalUnary⟩

end BEDC.Derived.WazewskiUniversalDendriteUp
