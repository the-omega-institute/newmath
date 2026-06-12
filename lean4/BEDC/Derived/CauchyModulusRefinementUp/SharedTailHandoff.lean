import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_shared_tail_handoff [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t q tailRead ->
        PkgSig bundle tailRead pkg ->
          UnaryHistory tailRead ∧ Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧
            Cont t q tailRead ∧ Cont q e h ∧ PkgSig bundle p pkg ∧
              PkgSig bundle tailRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro carrier tailRoute tailPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, _wUnary, qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed tUnary qUnary tailRoute
  exact ⟨tailUnary, m0m1u, uvt, twq, tailRoute, qeh, pPkg, tailPkg, hn⟩

theorem CauchyModulusRefinementSharedTailHandoff [AskSetup] [PackageSetup]
    {M0 M1 U V T W Q E H C P N sourceRead meetRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier M0 M1 U V T W Q E H C P N bundle pkg ->
      Cont M0 M1 sourceRead ->
        Cont sourceRead U meetRead ->
          Cont meetRead W tailRead ->
            Cont tailRead E sealRead ->
              PkgSig bundle sealRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M0 ∨ hsame row M1 ∨ hsame row U ∨ hsame row V ∨
                        hsame row T ∨ hsame row W ∨ hsame row Q ∨ hsame row E ∨
                          hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M0 M1 sourceRead ∧
                        Cont sourceRead U meetRead ∧ Cont meetRead W tailRead ∧
                          Cont tailRead E sealRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory meetRead ∧
                    UnaryHistory tailRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyModulusRefinementCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute meetRoute tailRoute sealRoute sealPkg
  rcases carrier with
    ⟨M0Unary, M1Unary, UUnary, _VUnary, _TUnary, WUnary, _QUnary, EUnary, _HUnary,
      _CUnary, _PUnary, _NUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, _hn⟩
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed M0Unary M1Unary sourceRoute
  have meetUnary : UnaryHistory meetRead :=
    unary_cont_closed sourceUnary UUnary meetRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed meetUnary WUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary EUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M0 ∨ hsame row M1 ∨ hsame row U ∨ hsame row V ∨
              hsame row T ∨ hsame row W ∨ hsame row Q ∨ hsame row E ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M0 M1 sourceRead ∧ Cont sourceRead U meetRead ∧
              Cont meetRead W tailRead ∧ Cont tailRead E sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, meetRoute, tailRoute, sealRoute, pPkg, sealPkg⟩
  }
  exact ⟨cert, sourceUnary, meetUnary, tailUnary, sealUnary⟩

end BEDC.Derived.CauchyModulusRefinementUp
