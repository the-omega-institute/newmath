import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierAuditRoute [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N windowRead classifierRead sealRead
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg →
      Cont W D windowRead →
        Cont windowRead C classifierRead →
          Cont classifierRead E sealRead →
            Cont sealRead K auditRead →
              PkgSig bundle auditRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
                        hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                          hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                            hsame row P ∨ hsame row N ∨ hsame row auditRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W D windowRead ∧
                        Cont windowRead C classifierRead ∧
                          Cont classifierRead E sealRead ∧ Cont sealRead K auditRead ∧
                            PkgSig bundle auditRead pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory classifierRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute classifierRoute sealRoute auditRoute auditPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, wUnary,
    dUnary, cUnary, eUnary, _hUnary, kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed windowUnary cUnary classifierRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed classifierUnary eUnary sealRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed sealUnary kUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
              hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                  hsame row P ∨ hsame row N ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D windowRead ∧
              Cont windowRead C classifierRead ∧ Cont classifierRead E sealRead ∧
                Cont sealRead K auditRead ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, classifierRoute, sealRoute, auditRoute, auditPkg⟩
  }
  exact ⟨cert, windowUnary, classifierUnary, sealUnary, auditUnary⟩

end BEDC.Derived
