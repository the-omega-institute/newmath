import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

namespace RealClassifierUp

theorem RealClassifierPsameBridgeConsumption [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N sealRead equalityRead realClassifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont X Y sealRead ->
        Cont sealRead C equalityRead ->
          Cont equalityRead N realClassifierRead ->
            PkgSig bundle realClassifierRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realClassifierRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row Y ∨ hsame row C ∨ hsame row N ∨
                      hsame row sealRead ∨ hsame row equalityRead ∨
                        hsame row realClassifierRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont X Y sealRead ∧
                      Cont sealRead C equalityRead ∧
                        Cont equalityRead N realClassifierRead ∧
                          PkgSig bundle realClassifierRead pkg)
                  hsame ∧
                UnaryHistory sealRead ∧ UnaryHistory equalityRead ∧
                  UnaryHistory realClassifierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sealRoute equalityRoute classifierRoute classifierPkg
  obtain ⟨xUnary, yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, _wUnary,
    _dUnary, cUnary, _eUnary, _hUnary, _kUnary, _pUnary, nUnary, _sealPkg⟩ :=
    carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed xUnary yUnary sealRoute
  have equalityUnary : UnaryHistory equalityRead :=
    unary_cont_closed sealUnary cUnary equalityRoute
  have classifierUnary : UnaryHistory realClassifierRead :=
    unary_cont_closed equalityUnary nUnary classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realClassifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row C ∨ hsame row N ∨
              hsame row sealRead ∨ hsame row equalityRead ∨
                hsame row realClassifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X Y sealRead ∧ Cont sealRead C equalityRead ∧
              Cont equalityRead N realClassifierRead ∧ PkgSig bundle realClassifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realClassifierRead
        ⟨hsame_refl realClassifierRead, classifierUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, equalityRoute, classifierRoute, classifierPkg⟩
  }
  exact ⟨cert, sealUnary, equalityUnary, classifierUnary⟩

end RealClassifierUp

end BEDC.Derived
