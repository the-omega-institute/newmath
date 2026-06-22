import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RealClassifierUp : Type where
  | packet : RealClassifierUp

def RealClassifierCarrier [AskSetup] [PackageSetup]
    (X Y SX SY RX RY W D C E H K P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory SX ∧ UnaryHistory SY ∧
    UnaryHistory RX ∧ UnaryHistory RY ∧ UnaryHistory W ∧ UnaryHistory D ∧
      UnaryHistory C ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory K ∧
        UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle E pkg

theorem RealClassifierRegSeqRatHandoff [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N regRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont SX RX regRead ->
        Cont regRead D classifierRead ->
          PkgSig bundle classifierRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row SX ∨ hsame row SY ∨ hsame row RX ∨ hsame row RY ∨
                    hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                      hsame row classifierRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont SX RX regRead ∧
                    Cont regRead D classifierRead ∧ PkgSig bundle classifierRead pkg)
                hsame ∧
              UnaryHistory regRead ∧ UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier regRoute classifierRoute classifierPkg
  obtain ⟨_xUnary, _yUnary, sxUnary, _syUnary, rxUnary, _ryUnary, _wUnary,
    dUnary, _cUnary, _eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed sxUnary rxUnary regRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed regUnary dUnary classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row SX ∨ hsame row SY ∨ hsame row RX ∨ hsame row RY ∨
              hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont SX RX regRead ∧ Cont regRead D classifierRead ∧
              PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead
        ⟨hsame_refl classifierRead, classifierUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regRoute, classifierRoute, classifierPkg⟩
  }
  exact ⟨cert, regUnary, classifierUnary⟩

end BEDC.Derived
