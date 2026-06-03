import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntermediateValueTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IntermediateValueTheoremCarrier [AskSetup] [PackageSetup]
    (I J F A B S R E H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory F ∧ UnaryHistory A ∧
    UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem IntermediateValueTheoremCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {I J F A B S R E H C P N signRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueTheoremCarrier I J F A B S R E H C P N bundle pkg ->
      Cont I J F ->
        Cont F A signRead ->
          Cont signRead R realRead ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row J ∨ hsame row F ∨ hsame row A ∨
                      hsame row B ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row signRead ∨ hsame row realRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont I J F ∧ Cont F A signRead ∧
                      Cont signRead R realRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle realRead pkg)
                  hsame ∧ UnaryHistory signRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier intervalLocated mapSign signReal realPkg
  obtain ⟨_iUnary, _jUnary, fUnary, aUnary, _bUnary, _sUnary, rUnary, _eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, pPkg, _nPkg⟩ := carrier
  have signUnary : UnaryHistory signRead :=
    unary_cont_closed fUnary aUnary mapSign
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed signUnary rUnary signReal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row J ∨ hsame row F ∨ hsame row A ∨
              hsame row B ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row signRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I J F ∧ Cont F A signRead ∧
              Cont signRead R realRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, intervalLocated, mapSign, signReal, pPkg, realPkg⟩
  }
  exact ⟨cert, signUnary, realUnary⟩

end BEDC.Derived.IntermediateValueTheoremUp
