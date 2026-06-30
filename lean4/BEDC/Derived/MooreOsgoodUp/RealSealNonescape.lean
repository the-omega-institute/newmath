import BEDC.Derived.MooreOsgoodUp.IteratedLimitHandoff
import BEDC.Derived.MooreOsgoodUp.UniformTailLock

namespace BEDC.Derived.MooreOsgoodUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MooreOsgoodCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {W F S U Q R D E H C P N uniformRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreOsgoodCarrier W F S U Q R D E H C P N bundle pkg ->
      Cont U Q uniformRead -> Cont uniformRead R regularRead ->
        Cont regularRead E sealRead -> PkgSig bundle sealRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row U ∨ hsame row Q ∨ hsame row R ∨ hsame row E ∨
                  hsame row uniformRead ∨ hsame row regularRead ∨ hsame row sealRead)
              (fun row : BHist =>
                hsame row sealRead ∧ Cont U Q uniformRead ∧
                  Cont uniformRead R regularRead ∧ Cont regularRead E sealRead ∧
                    PkgSig bundle sealRead pkg)
              hsame ∧ UnaryHistory uniformRead ∧ UnaryHistory regularRead ∧
            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier uniformRoute regularRoute sealRoute sealPkg
  obtain ⟨_wUnary, _fUnary, _sUnary, uUnary, qUnary, rUnary, _dUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed uUnary qUnary uniformRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed uniformUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row Q ∨ hsame row R ∨ hsame row E ∨
              hsame row uniformRead ∨ hsame row regularRead ∨ hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont U Q uniformRead ∧
              Cont uniformRead R regularRead ∧ Cont regularRead E sealRead ∧
                PkgSig bundle sealRead pkg)
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
                  (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, uniformRoute, regularRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, uniformUnary, regularUnary, sealUnary⟩

end BEDC.Derived.MooreOsgoodUp
