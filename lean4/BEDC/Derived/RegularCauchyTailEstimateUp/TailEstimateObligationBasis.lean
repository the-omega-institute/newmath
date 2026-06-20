import BEDC.Derived.RegularCauchyTailEstimateUp

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimateObligationBasis [AskSetup] [PackageSetup]
    {M W D R E H C P N sealRead tailRead dominanceRead dyadicRead triangleRead
      basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg ->
      UnaryHistory M ->
        UnaryHistory W ->
          UnaryHistory D ->
            UnaryHistory R ->
              UnaryHistory E ->
                Cont M W sealRead ->
                  Cont D R tailRead ->
                    Cont sealRead tailRead dominanceRead ->
                      Cont dominanceRead D dyadicRead ->
                        Cont dyadicRead E triangleRead ->
                          Cont triangleRead N basisRead ->
                            PkgSig bundle P pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                                      hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                                        hsame row N ∨ hsame row basisRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont M W sealRead ∧
                                      Cont D R tailRead ∧
                                        Cont sealRead tailRead dominanceRead ∧
                                          Cont dominanceRead D dyadicRead ∧
                                            Cont dyadicRead E triangleRead ∧
                                              Cont triangleRead N basisRead ∧
                                                PkgSig bundle P pkg)
                                  hsame ∧
                                UnaryHistory basisRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM unaryW unaryD unaryR unaryE sealRoute tailRoute dominanceRoute
    dyadicRoute triangleRoute basisRoute provenance
  obtain ⟨_carrierM, _carrierW, _carrierD, _carrierR, _carrierE, _unaryH, _unaryC,
    _unaryP, unaryN, _carrierPkg, _carrierName⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed unaryM unaryW sealRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed unaryD unaryR tailRoute
  have dominanceUnary : UnaryHistory dominanceRead :=
    unary_cont_closed sealUnary tailUnary dominanceRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed dominanceUnary unaryD dyadicRoute
  have triangleUnary : UnaryHistory triangleRead :=
    unary_cont_closed dyadicUnary unaryE triangleRoute
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed triangleUnary unaryN basisRoute
  have sourceBasis :
      (fun row : BHist => hsame row basisRead ∧ UnaryHistory row) basisRead := by
    exact ⟨hsame_refl basisRead, basisUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row basisRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M W sealRead ∧ Cont D R tailRead ∧
              Cont sealRead tailRead dominanceRead ∧ Cont dominanceRead D dyadicRead ∧
                Cont dyadicRead E triangleRead ∧ Cont triangleRead N basisRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro basisRead sourceBasis
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sealRoute, tailRoute, dominanceRoute, dyadicRoute, triangleRoute,
          basisRoute, provenance⟩
  }
  exact ⟨cert, basisUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
