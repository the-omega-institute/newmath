import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyNameUniformityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNameUniformityNameCertObligations [AskSetup] [PackageSetup]
    {S0 S1 W R0 R1 D E H C P N commonRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S0 ->
      UnaryHistory S1 ->
        UnaryHistory W ->
          UnaryHistory R0 ->
            UnaryHistory R1 ->
              UnaryHistory D ->
                UnaryHistory E ->
                  Cont S0 S1 commonRead ->
                    Cont commonRead W readbackRead ->
                      Cont readbackRead D sealRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row S0 ∨ hsame row S1 ∨ hsame row W ∨
                                  hsame row R0 ∨ hsame row R1 ∨ hsame row D ∨
                                    hsame row E ∨ hsame row commonRead ∨
                                      hsame row readbackRead ∨ hsame row sealRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont S0 S1 commonRead ∧
                                  Cont commonRead W readbackRead ∧
                                    Cont readbackRead D sealRead ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle N pkg)
                              hsame ∧
                              UnaryHistory commonRead ∧ UnaryHistory readbackRead ∧
                                UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro s0Unary s1Unary wUnary _r0Unary _r1Unary dUnary _eUnary
    streamCommon commonWindow windowSeal provenancePkg localNamePkg
  have commonReadUnary : UnaryHistory commonRead :=
    unary_cont_closed s0Unary s1Unary streamCommon
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed commonReadUnary wUnary commonWindow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary dUnary windowSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S0 ∨ hsame row S1 ∨ hsame row W ∨ hsame row R0 ∨
              hsame row R1 ∨ hsame row D ∨ hsame row E ∨ hsame row commonRead ∨
                hsame row readbackRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S0 S1 commonRead ∧
              Cont commonRead W readbackRead ∧ Cont readbackRead D sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, streamCommon, commonWindow, windowSeal, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, commonReadUnary, readbackReadUnary, sealReadUnary⟩

end BEDC.Derived.CauchyNameUniformityUp
