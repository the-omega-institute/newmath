import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCarrier [AskSetup] [PackageSetup] (S D R M Q E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory M ∧
    UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S D R M Q E H C P N streamRead modulusRead compatRead regseqRead sealRead
      structuralRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCarrier S D R M Q E H C P N bundle pkg ->
      Cont S D streamRead ->
        Cont streamRead M modulusRead ->
          Cont modulusRead Q compatRead ->
            Cont compatRead R regseqRead ->
              Cont regseqRead E sealRead ->
                Cont H C structuralRead ->
                  Cont P N namedRead ->
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row M ∨
                            hsame row Q ∨ hsame row E ∨ hsame row H ∨
                              hsame row C ∨ hsame row P ∨ hsame row N ∨
                                hsame row sealRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle N pkg)
                        hsame ∧ UnaryHistory streamRead ∧ UnaryHistory modulusRead ∧
                      UnaryHistory compatRead ∧ UnaryHistory regseqRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier streamRoute modulusRoute compatRoute regseqRoute sealRoute structuralRoute
    namedRoute
  obtain ⟨sUnary, dUnary, rUnary, mUnary, qUnary, eUnary, hUnary, cUnary, pUnary, nUnary,
    pkgP, pkgN⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sUnary dUnary streamRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed streamUnary mUnary modulusRoute
  have compatUnary : UnaryHistory compatRead :=
    unary_cont_closed modulusUnary qUnary compatRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed compatUnary rUnary regseqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary eUnary sealRoute
  have _structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  have _namedUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row M ∨ hsame row Q ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgP, pkgN⟩
  }
  exact ⟨cert, streamUnary, modulusUnary, compatUnary, regseqUnary, sealUnary⟩

end BEDC.Derived.CauchyUp
